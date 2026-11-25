# The neighboring-rectangle constituent bound from MW correctness

This module proves
`neighborRectangleConstituentLengthBound_of_aubertCorrectness`. It assumes two
explicit hypotheses:

- `hMW : MoeglinWaldspurger.AubertCorrectness.{uF, max uF uV} F T`. This is the
  published proposition, proved separately, saying that the Library's integer-line MW dual
  computes the actual adjusted Aubert dual. The cuspidal-carrier universe is
  instantiated at `max uF uV`, the carrier universe of the actual
  representations in the bound, so the heads in `hMW` have that same carrier.
- `hH : Aubert.HeadProductLeadingTermStatement.{uF, uV} F T`, the published
  head-product leading-term proposition.

From them it proves the proposition `NeighborRectangleConstituentLengthBound F T`
(module `SpehNeighborRectangleReduction`). Combined with
`spehNeighborProductIrreducibility_of_rectangle_bound`, this gives the exact
target `SpehNeighborProductIrreducibility` from `hH` and `hMW`. No unconditional
result is claimed here: both hypotheses stay explicit.

## Mathematical route

This follows Badulescu, *On p-adic Speh representations* (2014), proof of
Theorem 1(b)(ii) (retained `1110.5080.tex`, lines 174–185). Let `A` and `B` be
the heads of the centered rectangles `a(k+1,l)^ρ` and `a(k-1,l)^ρ`, and let `C`
be an irreducible subquotient of `A × B`. Taking duals, the dual `CD` of `C` is
an irreducible subquotient of the product of the duals of `A` and `B`. Those
duals are the heads of the transposed rectangles `a(l,k+1)^ρ` and
`a(l,k-1)^ρ` (Theorem 1(a)). So the label of `CD` is rank-lower than their sum.
Badulescu's endpoint argument (lines 184–185) then shows that the MW dual of
that label has segments of length at most `l`. By MW correctness, this MW dual
is the label of `C`.

## Lemmas

- `realize_rectangle_tadic` and `realize_dual_rectangle_tadic`: under the
  centering condition `x + b = -(r+d-2)/2`, the integer rectangle
  `rectangle b (r-1) (d-1)` realizes to `a(r,d)^ρ`, and its MW dual realizes to
  `a(d,r)^ρ`. They use `realize_rectangle` and `dual_rectangle`
  (`MoeglinWaldspurgerRectangleDual`).
- `isLanglandsHead_of_isLanglandsQuotient`: a weak Langlands quotient of a
  segment datum is a Langlands head of its multisegment. It uses the Library's
  `orderedMultisegmentHeadExistence`, `orderedMultisegmentHeadClassification`
  and `Multisegment.IsLanglandsHead.of_iso`.
- `exists_isLanglandsHead`: every multisegment has a head at its degree
  (Library `multisegmentHeadExistence`).
- `exists_adjusted_realize_dual`: let `A` be the weak Langlands quotient of a
  datum labeled `realize ρ x a`. Then some weak Langlands quotient `D` of a
  datum labeled `realize ρ x (dual a)` exists, and the actual adjusted
  operator sends the class of `A` to the class of `D`. The degree matches by
  `MoeglinWaldspurger.supportPreservation` and
  `realize_degree_eq_of_support_eq`. The equality of classes is `hMW`.
- `nonempty_iso_of_class_eq`: two irreducible representations with equal
  exact finite-length classes are isomorphic
  (`SmoothRep.ofRepresentation_eq_irreducible_iff`).
- `lengths_le_of_adjusted_rankLE`: suppose `C` and `CD` are weak Langlands
  quotients of data `dC` and `dCD`. Suppose the adjusted operator sends the
  class of `C` to that of `CD`. Suppose also that `dCD.multisegment` is
  rank-lower than `a(l,k+1)^ρ + a(l,k-1)^ρ`. Then every segment of
  `dC.multisegment` has length at most `l`. Proof: the Library's
  `neighborIntegerModel` writes `dCD.multisegment` as the realization, at
  offset `(k-l-1)/2`, of an integer multisegment. `exists_adjusted_realize_dual`
  gives a weak head `E` of the realized MW dual, whose class is the adjusted
  image of the class of `CD`. Involutivity (`Aubert.adjustedOperator_involutive`)
  makes the classes of `C` and `E` equal, so `C ≅ E`. Head classification
  then makes the label of `C` equal to the realized MW dual. Finally,
  `realized_dual_lengths_le_neighborIntegerModel endingBound` bounds its
  segment lengths by `l`. This uses the proved Library `EndingBound`.

## Proof of the main theorem

Let `x₁ = -(k+l-1)/2`. Then `a(k+1,l)^ρ` is `rectangle 0 k (l-1)` realized at
`x₁`, and `a(k-1,l)^ρ` is `rectangle 1 (k-2) (l-1)` realized at the same `x₁`.
Their MW duals realize to `a(l,k+1)^ρ` and `a(l,k-1)^ρ`. Below, `A`, `B` and
`C` are the given weak Langlands quotients.

1. `exists_adjusted_realize_dual` gives weak heads `AD` and `BD` of the dual
   rectangles. The adjusted operator sends the classes of `A` and `B` to theirs.
2. The lemma `Aubert.AdjustedProductConstituents.exists_adjusted_isSubquotient`
   (no hypotheses) gives an irreducible `CD`. The adjusted
   operator sends the class of `C` to the class of `CD`, and `CD` is a
   subquotient of the normalized product of `AD` and `BD`.
3. `exists_weakHead` (`SpehNeighborProductAssembly`) gives a weak head datum
   `dCD` of `CD`.
4. Clause 1 of `hH`, for the data of `AD`, `BD` and `CD`, says that
   `dCD.multisegment` is rank-lower than `a(l,k+1)^ρ + a(l,k-1)^ρ`.
5. `lengths_le_of_adjusted_rankLE` finishes the proof.

## Provenance

This is a derived internal proof of the internal proposition
`NeighborRectangleConstituentLengthBound`. The two hypotheses are published
Library propositions. `hMW` is `AubertCorrectness F T`, which
`UniversalAubertCorrectness` gives for every `p`, `F` and `T`. `hH` is the head-product leading-term
statement, proved in the Library as `Langlands.Aubert.headProductLeadingTerm`.
The integer-line endpoint estimate is the Library's
`realized_dual_lengths_le_neighborIntegerModel`, with `EndingBound` proved in
`MoeglinWaldspurgerEndingBoundProof`.
