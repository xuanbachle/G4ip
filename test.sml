signature TEST =
  sig
    (* [check A b]: check that the prover determines A to have truth value b,
       printing a useful message on standard output. *)
    val check : Prop.prop -> bool -> unit

    (* the above specialized to true and false *)
    val ctrue : Prop.prop -> unit
    val cfalse : Prop.prop -> unit

    (* a list of propositions along with their expected truth values *)
    val tests : (Prop.prop * bool) list
    val mytests: (Prop.prop * bool) list
    (* [runtests ()]: run all the tests in [tests], keeping an error count.
       prints status messages to standard output. *)
    val runtests : unit -> unit
  end

structure Test :> TEST =
struct
  structure G = G4ip
  structure P = Prop

  val ==> = P.Implies
  val & = P.And
  val v = P.Or
  val f = P.False
  val t = P.True
  val ~ = P.Not
  val <=> = fn (A,B) => P.And (P.Implies (A, B), P.Implies (B, A))
  val <== = fn (A,B) => P.Implies (B, A)

  infix 9 &
  infix 8 v
  infixr 7 ==>
  infix 7 <==
  infix 6 <=>
  val A = P.Atom("A")
  val B = P.Atom("B")
  val C = P.Atom("C")
  val D = P.Atom("D")
  val E = P.Atom("E")
  val F = P.Atom("F")

  val errors = ref 0

  fun check A expected =
    let val expected_str = (if not expected then " un" else " ") ^ "provable"
    in
        print ("Checking " ^ P.toString A ^ expected_str ^ "... ");
        if G.decide A = expected
         then print "\027[1;30m[\027[32m OK! \027[30m]\027[m\n"
         else (print "\027[1;30m[\027[31m WRONG \027[30m]\027[m\n";
               errors := !errors + 1)
    end

  fun cfalse (A) = check A false
  fun ctrue (A) = check A true

  (* tests : (P.prop * bool) list
     A list of propositions along with their expected truth values *)
  val tests =
  [
    (* I *) ( A ==> A , true ),
    (* K *) ( A ==> (B ==> A) , true ),
    (* S *) ( (A ==> B) ==> (A ==> (B ==> C)) ==> (A ==> C) , true ),

    (* Peirce's law -- not provable, generally *)
    ( ((A ==> B) ==> A) ==> A , false ),
    (* ... but by Glivenko's theorem, its double-negation should be! *)
    ( ~ (~ (((A ==> B) ==> A) ==> A)) , true ),

    (* andComm: *)
    ( A & B ==> B & A , true ),
    (* hw01, orComm: *)
    ( A v B ==> B v A , true ),

    (* hw01, clue: *)
    let val P = P.Atom "P"
        val S = P.Atom "S"
        val C = P.Atom "C"
        val D = P.Atom "D"
        val K = P.Atom "K"
        val L = P.Atom "L"
    in
        ( (P ==> (C & K) v (D & L))
            ==> (~K ==> S)
            ==> (D v L)
            ==> (P ==> ~S) & (S ==> ~P)
            ==> (C ==> ~D) & (D ==> ~C)
            ==> (K ==> ~L) & (L ==> ~K)
            ==> ~P , true )
    end,

    (* hw02, implOr: *)
    ( (A v C) & (B ==> C) ==> (A ==> B) ==> C, true ),

    (* some basic propositional (non-)tautologies *)
    ( (A ==> B ==> C) <=> (A & B ==> C) , true ),
    ( (A ==> B & C) <=> (A ==> B) & (A ==> C) , true ),
    ( (A ==> B v C) ==> (A ==> B) v (A ==> C) , false ),
    ( (A ==> B v C) <== (A ==> B) v (A ==> C) , true ),
    ( ((A ==> B) ==> C) ==> ((A v B) & (B ==> C)) , false ),
    ( ((A ==> B) ==> C) <== ((A v B) & (B ==> C)) , true ),
    ( (A v B ==> C) <=> (A ==> C) & (B ==> C) , true ),
    ( (A & (B v C)) <=> (A & B) v (A & C) , true ),
    ( (A v (B & C)) <=> (A v B) & (A v C) , true ),

    (* some deMorgan-like dualities *)
    ( ~ (A & B) ==> ~ A v ~ B , false ),
    ( ~ (A & B) <== ~ A v ~ B , true ),
    ( ~ (A v B) <=> ~ A & ~ B , true ),
    ( ~ (A ==> B) ==> A & ~ B , false ),
    ( ~ (A ==> B) <== A & ~ B , true ),
    ( ~ (~ A) ==> A , false ),
    ( ~ (~ A) <== A , true ),
    ( ~ t <=> f , true ),
    ( ~ f <=> t , true ),

    (* triple-negation elimination *)
    ( ~ (~ (~ A)) <=> ~ A , true ),
    (* three-way transitivity *)
    ( (A ==> B) ==> (B ==> C) ==> (C ==> D) ==> (A ==> D) , true ),

    (* some test cases for various common mistakes *)

    ( (A ==> B) ==> (A ==> C) ==> A ==> B , true ),
    ( (A ==> B) ==> (A ==> C) ==> A ==> C , true ),
    ( A ==> (A ==> B) ==> (A ==> C) ==> B , true ),
    ( A ==> (A ==> B) ==> (A ==> C) ==> C , true ),

    ( (A ==> B ==> C) ==> A ==> B ==> C , true ),
    ( (A ==> B ==> C) ==> B ==> A ==> C , true ),
    ( A ==> B ==> (A ==> B ==> C) ==> C , true ),
    ( B ==> A ==> (A ==> B ==> C) ==> C , true ),

    (* it turns out that heavily left-nested instances of the identity
       theorem make really great stress-tests for correctness! *)
    ( (A ==> B) ==> A ==> B , true ),
    ( ((A ==> B) ==> C) ==> ((A ==> B) ==> C) , true ),
    ( (((A ==> B) ==> C) ==> D) ==> (((A ==> B) ==> C) ==> D) , true ),
    ( ((((A ==> B) ==> C) ==> D) ==> E) ==> (((A ==> B) ==> C) ==> D) ==> E , true ),
    ( (((((A ==> B) ==> C) ==> D) ==> E) ==> F) ==> ((((A ==> B) ==> C) ==> D) ==> E) ==> F , true ),
    ( (((((A ==> B) ==> C) ==> D) ==> E) ==> F) ==> (((((A ==> B) ==> C) ==> D) ==> E) ==> F) v (((((A ==> B) ==> C) ==> D) ==> E) ==> F) , true ),

    ( ((A ==> B) ==> C) ==> D ==> D v D, true )
  ]
  
  val mytests = [((A & B ==> F) ==> (A ==> F) v (B ==> F), false)]
  fun runtests () =
    (errors := 0;
     List.app (fn (a, e) => check a e) tests;
     if !errors = 0
      then print "*** All tests passed!\n"
      else print ("*** " ^ Int.toString (!errors)
                  ^ " test(s) failed... see if you can fix them!\n"))
end

structure Main = struct
  val _ = Test.runtests ()
end
