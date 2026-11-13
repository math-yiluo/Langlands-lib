# Rank bounds and leading multiplicity for products of actual Langlands heads

This helper module proves the three clauses of the published proposition
`Langlands.Aubert.HeadProductLeadingTermStatement` as separate theorems in the
namespace `Langlands.Aubert.HeadProductLeadingTerm`. The exact-target wrapper
`Langlands.Aubert.headProductLeadingTerm` is in
[HeadProductLeadingTermProof](HeadProductLeadingTermProof.md).

The module has no hypotheses beyond the data of the statement. It does not use
the adjusted multisegment exchange or the socle-product statement
`SocleProductLeadingTermStatement`. The facts it needs about the adjusted Aubert
operator and about products of Zelevinsky labels come from the published module
[LanglandsHeadDuality](LanglandsHeadDuality.md) and from
`SegmentPolynomialSurjectivity`.

All classes, products and induction functors are the actual Library
constructions. The structural witnesses are the published theorems
`binaryProductExactness F T` (written `hx`) and `gradedInductionRingLaws F T hx`
(written `hl`). They give the ring `gradedInductionRing F T hx hl`, whose
multiplication is `gradedMultiplication F T hx`. Inside a proof of a proposition,
`HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T` supplies a unitary
additive character `ψ`.

## Notation

Write `ζ(a)` for `zeta F T hx hl a`, Zelevinsky's class `∏_{Δ ∈ a} ζ(Δ)` of the
product of the segment socles of a multisegment `a`, and `[c]` for `basisClass F T m c` when `c` is a label in rank
`m`. Write `coeff k e x` for the coefficient of the rank-`k` label `e` in `x`. A
class is effective when all its coefficients are nonnegative. "`c` is a label of
`a`" is `IsLabel F T a m c`: `c` is the class of the Zelevinsky socle of `a`.

## Helpers

`exists_head` restates the published `Classification.multisegmentHeadExistence`
at a rank `m` given by a degree equation `a.degree = m`.

`exists_socleLabel_of_isLanglandsQuotient` takes a datum `d` of rank `n` and a
representation `L` with `d.IsLanglandsQuotient L`. It produces a label `c` of
`d.multisegment` in rank `n` whose image under `gradedAdjustedOperator F T` is the
basis class of `L`. The proof proceeds as follows.

1. `LanglandsHeadDuality.exists_isLabel_of_degree` gives the label `c`.
2. `exists_head` gives a datum `da` and a representation `La` with the same
   multisegment and `da.IsLanglandsHead La`.
3. The published `LanglandsHeadDuality.gradedAdjustedOperator_label` sends `[c]`
   to the class of `La`.
4. The published `Classification.orderedMultisegmentHeadClassification` gives
   `La ≅ L`, because the two multisegments agree. So `La` and `L` have the same
   irreducible class.

The rank-zero case is included.

`coeff_mul_eq_compositionMultiplicity` takes labels `cA`, `cB` and `cC` whose
adjusted images are the classes of irreducible `A`, `B` and `C`. It shows that
`coeff (m + n) cC ([cA] * [cB])` equals the composition multiplicity of `C` in
the actual binary normalized product of `A` and `B`. The published
`LanglandsHeadDuality.coeff_gradedAdjustedOperator` transports the coefficient
along the adjusted operator. The published multiplicativity
`adjustedHomogeneousMultiplicativity`, through
`gradedOperator_multiplicative_of_homogeneous`, turns the image of the product
into the product of the images. `gradedMultiplication_homogeneous`,
`binaryProductK0_classes` and `coeff_gradedInclusion_ofRepresentation` identify
the result with the composition multiplicity.

## Products of labels

The section `Labels` takes arbitrary `hx`, `hl` and `ψ`. Let `c` be a label of
`a` in rank `m` and `d` a label of `b` in rank `n`. By
`one_le_coeff_zeta_of_isLabel`, `[c]` occurs in `ζ(a)` and `[d]` occurs in `ζ(b)`.
The classes `ζ(a)` and `ζ(b)` are effective (`isEffective_zeta`), so
`LanglandsHeadDuality.isEffective_mul_sub_basisClass_mul` shows that
`ζ(a) * ζ(b) - [c] * [d]` is effective. By `zeta_add`,
`ζ(a) * ζ(b) = ζ(a + b)`.

- `rankLE_of_coeff_label_mul_pos`. If `e` is a label of `q` in rank `k` and
  `coeff k e ([c] * [d]) > 0`, then the effective remainder gives
  `coeff k e ζ(a + b) > 0`. The published triangularity
  `rankLE_of_coeff_zeta_pos`, with the published step
  `highestDerivativeLabelStep F T ψ`, then gives `RankLE q (a + b)`.
- `coeff_label_mul_eq_one`. If `e` is a label of `a + b` in rank `m + n`, then
  `coeff (m + n) e ([c] * [d]) = 1`. The lower bound `1 ≤` is the published
  `LanglandsHeadDuality.one_le_coeff_label_mul`, the label form of Zelevinsky 1980,
  Proposition 8.4. For the upper bound, `LanglandsHeadDuality.coeff_zeta_eq_one_of_isLabel`
  gives `coeff (m + n) e ζ(a + b) = 1`, and the effective remainder bounds the
  coefficient in `[c] * [d]` by this value.

## Main results

Each main theorem fixes `hx := binaryProductExactness F T`,
`hl := gradedInductionRingLaws F T hx` and a character `ψ`. It then chooses
labels `cA`, `cB`, `cC` of the three multisegments with
`exists_socleLabel_of_isLanglandsQuotient`.

- `rankLE_of_isSubquotient` (clause 1). The product has finite length by
  `binaryProduct_preservesFiniteLength`. An actual subquotient has positive
  composition multiplicity (`compositionMultiplicity_pos_iff_isSubquotient`). By
  `coeff_mul_eq_compositionMultiplicity`, `coeff (m + n) cC ([cA] * [cB]) > 0`.
  `rankLE_of_coeff_label_mul_pos` then gives
  `RankLE dC.multisegment (dA.multisegment + dB.multisegment)`.
- `compositionMultiplicity_eq_one` (clause 2). If
  `dC.multisegment = dA.multisegment + dB.multisegment`, then `cC` is a label of
  the sum. `coeff_label_mul_eq_one` says its coefficient is one, and
  `coeff_mul_eq_compositionMultiplicity` turns this into composition multiplicity
  one for every finite-length certificate.
- `exists_longer_segment_of_isSubquotient` (clause 3) applies the internal
  combinatorial lemma `Multisegment.RankLE.exists_longer_segment` from
  [UniformLengthRankOrder](UniformLengthRankOrder.md) to the rank bound of
  clause 1.

## Provenance

The route is derived and internal; it is not a transcription of a numbered
literature theorem. Worker 597 wrote the first head-product proof in the previous
instance (Task 5496 draft revision 1). That version used internal helpers of the
then-unpublished adjusted multisegment exchange proof and of the socle-product
proof. Worker 5496 reworked it in Task 5496 draft revision 4 to use the published
`LanglandsHeadDuality` for the adjusted operator, with the socle-product
proposition as a hypothesis. Worker 32 replaced that hypothesis by the direct
label-product lemmas above, which use only published Library theorems.
