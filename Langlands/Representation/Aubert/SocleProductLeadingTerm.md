# Products of socle labels: rank triangularity and leading multiplicity one

Proof of the published proposition
`Langlands.Aubert.SocleProductLeadingTermStatement`
(`Aubert/SocleProductLeadingTermStatement`). Worker 104 and Worker 597 wrote
the proof development in an earlier project instance. Worker 97 added the final
wrapper theorem and this description.

## Final theorem

```lean
theorem Langlands.Aubert.socleProductLeadingTerm {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SocleProductLeadingTermStatement.{uF, uV} F T
```

Both universe parameters `uF` and `uV` are free, and the theorem has no
hypotheses beyond the prime `p`, the field `F` and its data `T`. The theorem
introduces the universally quantified witnesses
`hx : BinaryProductExactnessStatement F T` and
`hl : GradedInductionRingLawsStatement F T hx`. Its first clause is the lemma
`SocleProductLeadingTerm.rankLE_of_coeff_mul_pos`, and its second clause is
`SocleProductLeadingTerm.coeff_mul_eq_one`. The lemma `coeff_mul_eq_one` is
stated with the local ring instance `gradedInductionRing F T hx hl`, whose `*`
is by definition `gradedMultiplication F T hx`. So `exact` closes the second
clause without rewriting. The proof does not assume an Aubert exchange,
unitarity, Langlands-head triangularity, a Moeglin–Waldspurger result or a
replacement multiplication.

## Published inputs

- `Aubert/SegmentPolynomialSurjectivity`: coefficients `coeff`, basis
  classes `basisClass`, effectivity `IsEffective` (all coefficients
  nonnegative), the standard products `zeta` with `zeta_add`,
  `isEffective_zeta`, `isEffective_sub_basisClass`, `nonneg_of_isEffective`,
  `apply_eq_sum`, the weighted counts with `coeff_mul_le_weightedCount` and
  `labelWeight_of_isLabel`, and `exists_isLabel`. The module also supplies
  Zelevinsky's Theorem 7.1 for standard products, in the form
  `rankLE_of_coeff_zeta_pos` (triangularity), `labelCount_zeta_le_one` (the
  labels of `a` occur in `zeta a` with total multiplicity at most one) and
  `one_le_coeff_zeta_of_isLabel`.
- `highestDerivativeLabelStep` (proved) and
  `HarmonicAnalysis.padicUnitaryAdditiveCharacterExists`, which supply the
  additive character `ψ` and the step hypothesis required by those theorems.
- `Aubert/GradedGrothendieck`: `gradedMultiplication_homogeneous` and
  `binaryProductK0_classes`. These identify the product of two homogeneous
  classes of representations with the class of the actual normalized
  induced representation.
- `Aubert/BinaryProductExactnessProof` and `Aubert/GradedInductionRingLawsProof`
  for the ring structure `gradedInductionRing`.
- `Classification/MultisegmentSocleExhaustionProof`
  (`Classification.multisegmentSocleExhaustion`), which gives every
  irreducible basis label a multisegment `q` with `IsLabel q`.
- `Aubert/MultisegmentRankOrder` through the helper module
  `Aubert/RankOrderProducts`, which proves `Multisegment.RankLE.add`.

## Implemented proof

Fix `hx` and `hl`, and work in the ring `gradedInductionRing F T hx hl`.

**Effectivity of products.** In `isEffective_mul_basisClass`, write the two
irreducible labels as classes of actual irreducible representations `A` and
`B`. By `gradedMultiplication_homogeneous` and `binaryProductK0_classes`, the
product of their basis classes is the graded class of the actual finite-length
induced representation, which is effective by
`isEffective_gradedInclusion_ofRepresentation`. `isEffective_mul` extends this
to all effective `x` and `y`: it applies `nonneg_of_isEffective` twice to the
linear functionals `x ↦ coeff (x * y)` and `y ↦ coeff (basisClass * y)`.
Consequently (`coeff_mul_le_mul_right`), if `x' - x` and `y` are effective,
then `coeff (x * y) ≤ coeff (x' * y)` for every coefficient.

**Clause 1.** If `c` is a label of `a` and `d` is a label of `b`, then
`zeta a - basisClass c` and `zeta b - basisClass d` are effective. Two
applications of the previous inequality, with commutativity, give
`coeff_e (basisClass c * basisClass d) ≤ coeff_e (zeta a * zeta b) = coeff_e (zeta (a + b))`
(`coeff_mul_le_zeta`). Thus a positive coefficient of a label `e` of `q` in
the label product is positive in `zeta (a + b)`, and
`rankLE_of_coeff_zeta_pos` gives `RankLE q (a + b)`
(`rankLE_of_coeff_mul_pos`).

**Leading coefficient of a standard product.** For a label `c` of `a`,
`coeff_c (zeta a) = 1` (`coeff_zeta_eq_one_of_isLabel`). The lower bound is
`one_le_coeff_zeta_of_isLabel`. For the upper bound, `coeff_mul_le_weightedCount`
with the label-indicator weight of `a` bounds the coefficient by the weighted
label count, which is at most one by `labelCount_zeta_le_one`.

**Remainder labels are strictly lower.** In `rankLT_of_coeff_remainder_ne_zero`,
let `e` be a label of `q` with nonzero coefficient in the effective remainder
`zeta a - basisClass c`. That coefficient is positive, so the coefficient of `e`
in `zeta a` is positive, and triangularity gives `RankLE q a`. If `q = a`,
then `e` is also a label of `a`. The weighted label count of the remainder is
at most `1 - 1 = 0`, by `weightedCount_basisClass` and
`labelCount_zeta_le_one`. This contradicts the positive coefficient of `e`.
Hence `q ≠ a`.

**Remainders do not reach the label of `a + b`.** Let `e` be a label of
`a + b`, and let `q` be strictly rank-lower than `a`. If `e` had a positive
coefficient in `zeta (q + b)`, triangularity would give
`RankLE (a + b) (q + b)`. `RankLE.add` gives `RankLE (q + b) (a + b)`, so
antisymmetry and additive cancellation of multisets give `q = a`, a
contradiction (`coeff_zeta_add_eq_zero_of_rankLT`). Now expand the remainder
`zeta a - basisClass c` in the basis (`apply_eq_zero_of_coeff`, a finite-sum
consequence of `apply_eq_sum`). For each basis label `d` with nonzero
coefficient, socle exhaustion gives a multisegment `q` with `IsLabel q d`. By
the previous step, `q` is strictly lower than `a`. Then
`0 ≤ coeff_e (basisClass d * zeta b) ≤ coeff_e (zeta q * zeta b) = coeff_e (zeta (q + b)) = 0`.
Hence `coeff_e ((zeta a - basisClass c) * zeta b) = 0`
(`coeff_remainder_mul_zeta_eq_zero`).

**Clause 2** (`coeff_mul_eq_one`). Let `c`, `d` and `e` be labels of `a`, `b`
and `a + b`, so `e` is also a label of `b + a`. The symmetric instance of the
previous step, with commutativity, shows that
`coeff_e (basisClass c * (zeta b - basisClass d))` is at most `0`. Effectivity
shows that it is at least `0`, so it equals `0`. Write
`zeta a * zeta b = (zeta a - basisClass c) * zeta b + basisClass c * (zeta b - basisClass d) + basisClass c * basisClass d`.
The first two terms have coefficient zero at `e`, and
`coeff_e (zeta (a + b)) = 1`. Linear arithmetic therefore gives
`coeff_e (basisClass c * basisClass d) = 1`.

All statements are about the actual graded finite-length Grothendieck group
and cover every natural rank, including zero. The field universe `uF` and the
representation-carrier universe `uV` are independent throughout.

## Provenance

This is a derived proof from published Library results. Its mathematical
source is the standard-product triangularity and multiplicity one of
Zelevinsky 1980, Theorem 7.1, as already implemented in
`SegmentPolynomialSurjectivity`. The order is the published containment-count
order `Multisegment.RankLE`; no identification with Zelevinsky's
elementary-operation order is asserted.
