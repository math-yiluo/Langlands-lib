# Proof of product-Levi square-integrability from strict upper Jacquet exponents

Author: Worker 728.

This module proves the core statement of
[`ProductLeviSquareIntegrableSufficiencyStatement`](ProductLeviSquareIntegrableSufficiencyStatement.md):

```text
theorem Langlands.glProductLeviSquareIntegrableExponentSufficiency :
    GLProductLeviSquareIntegrableExponentSufficiencyStatement.{uF, uV}
```

The field and representation universes `uF` and `uV` stay independent. The
statement is imported by its Lean name and is not modified. Auxiliary
declarations are in the namespace `Langlands.ProductLeviSquareIntegrable`.
Two of them do not assume irreducibility and can be reused:
`isOpen_ker_of_isSmooth_of_isGeneralizedEigencharacter` (for any smooth
complex representation of a topological group) and
`memLp_two_of_strictFundHypothesis` (for any admissible representation).

The proof is the sufficiency half of Casselman's criterion (Theorem 4.4.6 of
the 1995 notes; Waldspurger 2003, Proposition III.1.1, (iii) ⇒ (i)) for the
product Levi `M_C`. It is assembled from the published strict chamber bound of
[`ProductLeviStrictChamberBound`](ProductLeviStrictChamberBound.md) and the
cell summation of
[`ProductLeviTemperedSufficiencyProof`](ProductLeviTemperedSufficiencyProof.md),
run at exponent `2`. The sources are cited in the statement's Markdown.

## Generalized eigencharacters have open kernels

`pow_sub_smul_apply_of_fixed`: if `π a v = v`, then
`(π a - c • 1) ^ k v = (1 - c) ^ k • v`, by induction on `k`.

`isOpen_ker_of_isSmooth_of_isGeneralizedEigencharacter` holds for any group
`A` with a topology in which multiplication is separately continuous (in
particular any topological group), any smooth complex representation `π` of
`A` and any generalized eigencharacter `χ`. By `isGeneralizedEigencharacter_iff` there are `k` and
`v ≠ 0` with `(π a - χ a • 1) ^ k v = 0` for all `a`. Smoothness gives an open
subgroup `U` fixing `v`. For `u ∈ U` the lemma above gives
`(1 - χ u) ^ k • v = 0`, so `χ u = 1`. Hence `U ≤ χ.ker`, and a subgroup that
contains an open subgroup is open (`Subgroup.isOpen_mono`).

`isOpen_ker_of_isGeneralizedEigencharacter_refined` applies this to the
pullback of `T.normalizedRefinedJacquet C D ρ` along
`flattenedLeviEquiv F.Carrier C D` and the flattened `blockScalarLevi`. The
pullback is smooth by `isSmooth_comp` and `isSmooth_normalizedRefinedJacquet`.
The pulling-back map is continuous because the block scalar embedding
(`GeneralLinear.scalarContinuous` in each factor) and `flattenedLeviEquiv`
(`flattenedLeviEquivContinuous`) are. This is the same argument as in the
published `ProductLeviSquareIntegrable.exists_character_of_eigenvalue`.

So the open-kernel assumption of the core hypothesis is no restriction: the
hypothesis applies to every generalized eigencharacter.

## The strict fundamental bound

`strictFundHypothesis_of_core` derives the published
`StrictFundHypothesis T C ρ` of
[`ProductLeviSquareIntegrableExponent`](ProductLeviSquareIntegrableExponent.md)
from the core hypothesis of the statement. Fix a fundamental index `s` and a
generalized eigencharacter `ψ` for the refinement `D = fundRefinement C s`.
Its kernel is open by the previous section. Apply the core hypothesis to `D`,
`ψ` and the flattened fundamental scalars
`a = flatScalars C D (fundScalars T C s)`:

- `flatScalars_apply` identifies `a (e(j,i))` with `fundScalars T C s j i`.
- Monotonicity in each outer block is the published
  `monotone_abs_of_isWeaklyContracting`, applied to
  `(fundScalars_isStrictlyContracting T C s j).weak`.
- In the outer block `j = s.1` the refinement has length `2`
  (`Function.update_self`). The inner scalars there are `ϖ` and `1`. By
  `uniformizer_abs` their absolute values are `q⁻¹` and `1`, which differ
  because `q > 1` (`residueCardinality_gt_one_real`).

The strict conjunct of the core hypothesis therefore gives
`‖ψ a‖ < 1`, which is `StrictFundHypothesis T C ρ`. The weak conjunct is not
used.

## The `L²` estimate

`memLp_two_of_strictFundHypothesis` follows the published proof of
`ProductLeviSquareIntegrable.memLp_of_strict` in
[`ProductLeviSquareIntegrableLpProof`](ProductLeviSquareIntegrableLpProof.md)
with the exponent `P = 2` in place of a `P < 2`. Given the Cartan coset count,
an admissible `ρ` with `StrictFundHypothesis T C ρ`, a unitary central
character `c`, a smooth functional `ℓ` and a vector `v`:

- `strict_cell_coefficient_bound` gives `ε > 0` and `cb` with
  `‖ℓ(ρ(k₁ · leviRep lam · k₂) v)‖ ≤ cb · ∏ j, delta T (lam j) ^ (1/2 + ε)` for
  all blockwise normalized `lam` and `k₁, k₂` in the integral Levi.
- With `w_s = fundWeight T C s ∈ (0, 1)` and `y_s = w_s ^ (1/2 + ε)`, the
  coefficient norm is at most `|cb| ∏ s, y_s ^ m s` on the cell
  `cellQ (latticeTuple m)` (`prod_delta_latticeTuple`).
- `measure_cellQ_le` bounds the cell measure by
  `∏ j, cc_j · delta(lam_j)⁻¹` times the finite measure of the image of the
  integral Levi (`measure_image_integralLevi_lt_top`).
- The square of the bound times the cell measure is at most a constant times
  `∏ s, x_s ^ m s` with `x_s = y_s ^ 2 · w_s⁻¹ = w_s ^ (2ε) < 1`, because
  `(1/2 + ε) · 2 − 1 = 2ε`.
- `finiteNatLatticeENNRealSummability` sums these terms over
  `FundIndex C → ℕ`. The cells cover the central quotient (`exists_cell`,
  `latticeTuple_fundCoeff`), and `countableCellLpUpper` gives `MemLp` for
  `ENNReal.ofReal 2 = 2`. Almost-everywhere strong measurability comes from
  `UnitaryCentralCharacter.aestronglyMeasurable_coefficientNorm`.

The estimate is for every Borel Haar measure `μ` on the central quotient,
since `measure_cellQ_le` uses only left invariance.

## Assembly

`squareIntegrable_of_cellCount` proves the statement from the Cartan coset
count `CartanQuotient.CartanCellCountStatement`. The carrier of `S` is
nontrivial because `S` is irreducible (`IsSimpleModule.nontrivial`). The
unitary central character is the published
`unitaryCentralCharacterOfBlockScalar`, built from the scalar character `ω`
and its unitarity. Admissibility is a hypothesis. The coefficients are in `L²`
by `memLp_two_of_strictFundHypothesis` and `strictFundHypothesis_of_core`.

The final theorem applies `squareIntegrable_of_cellCount` to the published
proof `Langlands.GeneralLinear.CartanQuotient.cartanCellCount`.

## Imports

- `ProductLeviSquareIntegrableSufficiencyStatement` (the target);
- `ProductLeviStrictChamberBound` (strict chamber and cell bounds, and through
  it `StrictFundHypothesis`);
- `ProductLeviTemperedSufficiencyProof` (cells, cell measures, lattice
  tuples, and through its imports the cell `L^p` criterion and the lattice
  summability).
