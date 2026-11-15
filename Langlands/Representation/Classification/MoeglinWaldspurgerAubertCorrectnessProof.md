# Aubert correctness of the Moeglin–Waldspurger multisegment recursion

This module proves the Library statement
`Langlands.MoeglinWaldspurger.UniversalAubertCorrectness.{uF, uV}`. The field universe `uF`
and the cuspidal-carrier universe `uV` are independent. The theorem has no hypotheses.

The statement says: for every prime `p`, every actual `p`-adic field `F` with topological
data `T`, every cuspidal datum `ρ`, real shift `x` and multisegment `a`, take irreducible
Langlands heads `π` of `realize ρ x a` and `πdual` of `realize ρ x (dual a)`. Here `dual` is
the Moeglin–Waldspurger recursion. Then the support-adjusted Aubert operator
`Aubert.adjustedOperator F T n` sends the finite-length class of `π` to the class of `πdual`.

## Declarations

* `universalAubertCorrectness_of_leftCuspidalDerivativeLemma hL` proves the statement from
  any proof `hL` of
  `Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma.{uF, uV}`.
  It applies the conditional theorem
  `Derivation.universalAubertCorrectness_of_interfaces` from module
  `MoeglinWaldspurgerConditionalCorrectness` to `hL` and to the Library theorem
  `Langlands.Classification.langlandsSubrepresentationRealization`.
* `universalAubertCorrectness : UniversalAubertCorrectness.{uF, uV}` is the final theorem.
  It supplies the Library theorem
  `Langlands.Classification.LeftCuspidalDerivative.leftCuspidalDerivativeLemma` as `hL`.

## The proof route

The work is done in the helper modules of this submission. The conditional theorem
`universalAubertCorrectness_of_interfaces` assumes two Library propositions:

1. `LeftCuspidalDerivativeLemma`: the highest left cuspidal derivative lemma for `GL_n`. It
   covers left-reduced representations and their products, and the comparison and uniqueness
   of highest left derivatives with respect to a cuspidal representation.
2. `LanglandsSubrepresentationRealization`: for a segment product datum in which no later
   segment precedes an earlier one, the Langlands heads of its multisegment are exactly the
   irreducible subrepresentations of its normalized induction.

From these two propositions the helper modules derive the proof in three steps:

* `derivativeFacts_LDrel` (module `MoeglinWaldspurgerConditionalCorrectness`) shows that the
  concrete highest left derivative relation `LDrel` satisfies the five derivative facts of
  module `MoeglinWaldspurgerLabelInduction`.
* `labelClass_of_headClass` (module `MoeglinWaldspurgerLabelInduction`) uses these facts and
  the proved combinatorial statements `topUnmatchedCompatibility` and
  `chainUnmatchedCompatibility`. It shows, by strong induction on the weight, that the class
  of every Langlands head of `a` is a weak Zelevinsky label of `dual a`.
* `universalAubertCorrectness_of_labelCorrectness` (module `MoeglinWaldspurgerAubertAssembly`)
  turns this label statement into the target, using the Library's Theorem P
  (`Aubert.LanglandsHeadDuality.gradedAdjustedOperator_label`).

Each helper module's Markdown file describes its part of the proof.

The Library already contains proofs of both propositions:
`leftCuspidalDerivativeLemma` (module `LeftCuspidalDerivativeProof`) and
`langlandsSubrepresentationRealization` (module `LanglandsSubrepresentationProof`). This module
imports both and applies the conditional theorem to them.
