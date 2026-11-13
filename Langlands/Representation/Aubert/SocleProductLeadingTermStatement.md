# Rank triangularity and leading multiplicity for products of socle labels

Author: Worker 594. The target and derived proof route were proposed by Worker 104.

`Langlands.Aubert.SocleProductLeadingTermStatement.{uF,uV} F T` is a
**new unproved proposition target**. This module defines the proposition and
provides no theorem proving it.

For arbitrary `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`, and
`T : F.TopologicalData`, the proposition universally quantifies
`hx : BinaryProductExactnessStatement.{uF,uV} F T` and
`hl : GradedInductionRingLawsStatement F T hx`. These are the existing
structural statements, already proved by `Langlands.Aubert.binaryProductExactness`
and `Langlands.Aubert.gradedInductionRingLaws`; they introduce no new
mathematical premise. The binder for the ring-law witness is named `_hl` in
Lean because the actual multiplication depends only on `hx`.

The field universe `uF` and representation-carrier parameter `uV` are
independent. Multisegments have the existing type
`T.Multisegment.{max uF uV,uF}`. At rank `m`, labels have the existing type
`SegmentPolynomialSurjectivity.Label.{uF,uV} F T m`, for actual irreducible
smooth complex representations with carriers in `Type (max uF uV)`.
The topology is the supplied `T.topology`.

The proposition has two conclusions, using the existing `IsLabel` relation.
This relation exhibits an actual irreducible subrepresentation of a
precedence-ordered product of segment socles, with the given multisegment.
It makes no choice of a label function.

1. For multisegments `a`, `b`, `q` and labels `c`, `d`, `e` of these
   multisegments at ranks `m`, `n`, `k`, respectively, a positive coefficient
   of `e` in the actual product of the basis classes of `c` and `d` implies
   `Multisegment.RankLE q (a + b)`.
2. For labels `c`, `d`, `e` of `a`, `b`, `a + b` at ranks `m`, `n`, `k`,
   respectively, the coefficient of `e` in that same product is exactly one.

Both clauses quantify all natural ranks, including zero. No separate degree
equalities are imposed: `IsLabel.degree` supplies the degrees of the
multisegments, and coefficients are read in the independently quantified rank
`k`. The operations are exactly `SegmentPolynomialSurjectivity.coeff`,
`SegmentPolynomialSurjectivity.basisClass`, and
`gradedMultiplication F T hx` on the existing graded finite-length
Grothendieck group. Thus using the proposition requires no local ring
instance. The product retains the actual normalized induction, its positive
half-modulus convention, and the exact Grothendieck relations from short
exact sequences.

## Derived provenance

This is an internal target derived from published Library mathematics. Its
source motivation is the standard-product triangularity and multiplicity
one of Zelevinsky 1980, Theorem 7.1, as implemented in
`Langlands.Representation.Aubert.SegmentPolynomialSurjectivity`. That
module's `rankLE_of_coeff_zeta_pos`, `labelCount_zeta_le_one`,
`one_le_coeff_zeta_of_isLabel`, and proved `highestDerivativeLabelStep`
provide the relevant standard-product results. The order here is precisely
the published containment-count order `Multisegment.RankLE` from
`Aubert/MultisegmentRankOrder`. No identification with Zelevinsky's
elementary-operation order is asserted.

The intended derivation uses positivity of actual induction: the product of
two irreducible basis classes is the class of the actual finite-length
induced representation, so all its coefficients are nonnegative.
`binaryProductK0_classes` and the published coefficient description express
this directly; bilinearity extends positivity to effective classes.
Removing a socle label from each standard product leaves an effective
remainder. Their product comparison bounds the product of the chosen labels
by the standard product of `a + b`, giving the first clause.

For the second clause, the published standard-product label count forces
each remainder label to be strictly lower in rank order. Published socle
exhaustion, `Langlands.Classification.multisegmentSocleExhaustion`, supplies
multisegment labels for the remainder constituents. Cuspidal content and
every containment count are additive under multisegment addition, so rank
inequalities add and cancel a common summand. If a strictly lower remainder
could contribute to the label of `a + b`, standard-product triangularity,
additivity, antisymmetry, and multiset cancellation would force that remainder
label to equal the removed multisegment. The contradiction makes the
remainder contribution zero. The remaining coefficient is the
standard-product coefficient, which is one.

This derivation is described to specify the target's provenance; it is not
implemented in this module. It requires no unitarity, Aubert exchange, or
replacement multiplication. It asserts neither irreducibility of the
whole product nor the Speh neighbor-product theorem. The sole import is the
published `SegmentPolynomialSurjectivity` module. All existing statements
and their import closures are preserved.
