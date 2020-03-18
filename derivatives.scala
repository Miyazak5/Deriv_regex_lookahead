import scala.util.parsing.combinator._

case class DFA[Q, A](
  state: Set[Q],
  alpha: Set[A],
  start: Q,
  fin: Set[Q],
  trans: Map[(Q, A), Q])

sealed trait RE {
  def derivM(c: Char): RE
  def derivL(c: Char): RE
  def norm: RE
  def isEnd: Boolean
  def alpha: Set[Char]
  def <=(r: RE): Boolean
  def print: String

  def toDFA: DFA[RE, Either[Char, Char]] = {
    var q0 = this.norm
    var reach = Set(q0)
    var stack = Set(q0)
    var t: Map[(RE, Either[Char, Char]), RE] = Map()

    while (! stack.isEmpty){
      val q = stack.head
      stack = stack.tail
      alpha.foreach{a =>
        val q2 = q.derivM(a)
        t += (((q, Right(a)), q2))
        if(! reach(q2)) stack += q2
        reach += q2
      }
      alpha.foreach{a =>
        val q2 = q.derivL(a)
        t += (((q, Left(a)), q2))
        if(! reach(q2)) stack += q2
        reach += q2
      }
    }

    DFA(reach,
        alpha.map(Right(_)) ++ alpha.map(Left(_)),
        q0,
        reach.filter(_.isEnd),
        t)
  }

  def nPlus(r1: RE, r2: RE): RE = (r1, r2) match {
    case (Zero, r) => r
    case (r, Zero) => r
    case (Plus(r, s), t) => nPlus(r, nPlus(s, t))
    case (r, Plus(s, t)) => {
      if(r == s) Plus(s, t)
      else if(r <= s) Plus(r, Plus(s, t))
      else Plus(s, nPlus(r, t))
    }
    case (r, s) => {
      if(r == s) r
      else if(r <= s) Plus(r, s)
      else Plus(s, r)
    }
  }

  def nTimes(r1: RE, r2: RE): RE = (r1, r2) match {
    case (Zero, _) => Zero
    case (_, Zero) => Zero
    case (One, r) => r
    case (r, One) => r
    case (Plus(r, s), t) => nPlus(nTimes(r, t), nTimes(s, t))
    case (r, Plus(s, t)) => nPlus(nTimes(r, s), nTimes(r, t))
    case (Times(r, s), t) => nTimes(r, nTimes(s, t))
    case (r: Not, Times(s: Not, t)) => {
      if(r == s) Times(s, t)
      else if(r <= s) Times(r, Times(s, t))
      else Times(s, nTimes(r, t))
    }
    case (r: Not, s: Not) => {
      if(r == s) r
      else if(r <= s) Times(r, s)
      else Times(s, r)
    }
    case (r, s) => Times(r, s)
  }

  def nNot(r: RE): RE = r match {
    case Zero => One
    case One => Zero
    case Plus(r, s) => nTimes(nNot(r), nNot(s))
    case Times(r: Not, s) => nPlus(nNot(r), nNot(s))
    case r => Not(r)
  }
}

case object Zero extends RE {
  def derivM(c: Char) = Zero
  def derivL(c: Char) = Zero
  def norm: RE = Zero
  def isEnd: Boolean = false
  def alpha = Set()
  def <=(r: RE): Boolean = true
  def print: String = "0"
}

case object One extends RE {
  def derivM(c: Char) = Zero
  def derivL(c: Char) = One
  def norm: RE = One
  def isEnd: Boolean = true
  def alpha = Set()
  def <=(r: RE): Boolean = r match {
    case Zero => false
    case _ => true
  }
  def print: String = "1"
}

case class Atom(a: String) extends RE {
  def derivM(c: Char) = if(a.contains(c)) One else Zero
  def derivL(c: Char) = Zero
  def norm: RE = Atom(a)
  def isEnd: Boolean = false
  def alpha = a.toSet
  def <=(r: RE): Boolean = r match {
    case Zero | One => false
    case Atom(b) => (a <= b)
    case _ => true
  }
  def print: String = {
    if (a.size == 1) a.toString
    else "[" + a.toString + "]"
  }
}

case class Plus(e1: RE, e2: RE) extends RE {
  def derivM(c: Char) = nPlus(e1.derivM(c), e2.derivM(c))
  def derivL(c: Char) = nPlus(e1.derivL(c), e2.derivL(c))
  def norm: RE = nPlus(e1.norm, e2.norm)
  def isEnd: Boolean = e1.isEnd || e2.isEnd
  def alpha = e1.alpha ++ e2.alpha
  def <=(r: RE): Boolean = r match {
    case Zero | One | Atom(_) => false
    case Plus(r1, r2) => if(e1 == r1) e2 <= r2 else e1 <= r1
    case _ => true
  }
  def print: String = e1.print + "|" + e2.print
}

case class Times(e1: RE, e2: RE) extends RE {
  def derivM(c: Char) = nPlus(nTimes(e1.derivM(c), e2), nTimes(e1.derivL(c), e2.derivM(c)))
  def derivL(c: Char) = nTimes(e1.derivL(c), e2.derivL(c))
  def norm: RE = nTimes(e1.norm, e2.norm)
  def isEnd: Boolean = e1.isEnd && e2.isEnd
  def alpha = e1.alpha ++ e2.alpha
  def <=(r: RE): Boolean = r match {
    case Zero | One | Atom(_) | Plus(_, _) => false
    case Times(r1, r2) => if(e1 == r1) e2 <= r2 else e1 <= r1
    case _ => true
  }
  def print: String = (e1, e2) match {
    case (e1: Plus, e2: Plus) => "(" + e1.print + ")(" + e2.print + ")"
    case (e1: Plus, _) => "(" + e1.print + ")" + e2.print
    case (_, e2: Plus) => e1.print + "(" + e2.print + ")"
    case _ => e1.print + e2.print
  }
}

case class Star(e: RE) extends RE {
  def derivM(c: Char) = nTimes(e.derivM(c), this)
  def derivL(c: Char) = One
  def norm: RE = Star(e.norm)
  def isEnd: Boolean = true
  def alpha = e.alpha
  def <=(r: RE): Boolean = r match {
    case Zero | One | Atom(_) | Plus(_, _) | Times(_, _) => false
    case Star(s) => e <= s
    case _ => true
  }
  def print: String = e match {
    case Plus(_, _) | Times(_, _) => "(" + e.print + ")*"
    case _ => e.print + "*"
  }
}

case class Not(e: RE) extends RE {
  def derivM(c: Char) = Zero
  def derivL(c: Char) = nNot(nPlus(e.derivM(c), e.derivL(c)))
  def norm: RE = nNot(e.norm)
  def isEnd: Boolean = ! e.isEnd
  def alpha = e.alpha
  def <=(r: RE): Boolean = r match {
    case Zero | One | Atom(_) | Plus(_, _) | Times(_, _) | Star(_) => false
    case Not(s) => e <= s
  }
  def print: String = e match {
    case Plus(_, _) | Times(_, _) | Not(_) => "!(" + e.print + ")"
    case _ => "!" + e.print
  }
}

object REParser extends RegexParsers {
  def exp: Parser[RE] = conc ~ "|" ~ exp ^^ { case r1 ~ b ~ r2 => Plus(r1, r2) } | conc
  def conc: Parser[RE] = pre ~ conc ^^ { case r1 ~ r2 => Times(r1, r2) } | "" ^^ { s => One }
  def pre = opt("[&!]".r) ~ suf ^^ {
    case Some(la) ~ r => {
      if (la == "&") Not(Not(r))
      else Not(r)
    }
    case None ~ r => r
  }
  def suf = elem ~ opt("*") ^^ {
    case f ~ Some(_) => Star(f)
    case f ~ None    => f
  }
  def elem = atom | lit | group
  def atom = "[a-z]".r ^^ { s => Atom(s) }
  def lit = "[" ~> "[a-z]+".r <~ "]" ^^ { s => Atom(s.toSeq.sorted.distinct.unwrap) }
  def group = "(" ~> exp <~ ")"

  def apply(input: String): RE = parseAll(exp, input) match {
    case Success(matchData, next)      => matchData
    case NoSuccess(errorMessage, next) => Zero
  }
}

object Main {
  def state(e: RE): Set[RE] = {
    var q0 = e.norm
    var alpha = e.alpha
    var reach = Set(q0)
    var stack = Set(q0)

    while (! stack.isEmpty){
      val q = stack.head
      stack = stack.tail
      alpha.foreach{ a =>
        val q2 = q.derivM(a)
        if(! reach(q2)) stack += q2
        reach += q2
      }
      alpha.foreach{ a =>
        val q2 = q.derivL(a)
        if(! reach(q2)) stack += q2
        reach += q2
      }
    }

    reach
  }

  def test(): Unit = {
    val es = List("a|b", "a*", "a!b", "a&b", "!(ab)a", "(!(ab)a)*", "(!(ab)(a|b|c))*", "ba(!(ab)[abc])*ab")
    for(e <- es) {
      val r = REParser(e)
      val s = state(r)
      println(e + "  => " + s.size + " " + s.map(_.print))
    }
  }

  def gen(xs: List[Int]): String = {
    val dot = "[ab]"
    val end = "!" + dot
    val all = dot + "*"
    def la(n: Int): String = "&(" + "(" + dot * n + ")*" + end + ")"
    all + "a" + xs.map(la(_)).mkString + all + end
  }

  def test2(): Unit = {
    val e = gen(List(3, 5))
    val r = REParser(e)
    val s = state(r)
    println(e + "  => " + s.size)
  }

  def main(args: Array[String]): Unit = {
    test()
    test2()
  }
}
