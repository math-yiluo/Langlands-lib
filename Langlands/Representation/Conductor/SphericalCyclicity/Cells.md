# The big cell of the `(1, n + 1)` block decomposition

Author: Worker 392.

This helper module of the proof of
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` (see
[`OrderedUnramifiedSphericalCyclicity`](../OrderedUnramifiedSphericalCyclicity.md))
works over a field `F` with `ValuativeRel F`. Write `v` for
`ValuativeRel.valuation F` and `𝒪` for its integer ring. The definitions are
internal auxiliary constructions, with no literature source. All declarations are
in `Langlands.Conductor.SphericalCyclicity`. The block notation `blk`, `rowT`,
`colT`, `low`, `blockDiag` and `lowerUnip` is from [`Blocks`](Blocks.md).

## Valuation helpers

- `val_le_one_of_mem` and `mem_of_val_le_one`: `x ∈ 𝒪 ↔ v x ≤ 1`.
- `val_mul_lt_one`: `v x ≤ 1` and `v y < 1` imply `v (x y) < 1`.
- `val_eq_one_of_mul_eq_one`: if `v a, v b ≤ 1` and `v (a b) = 1`, then
  `v a = v b = 1`.
- `mulVec_val_lt_one` and `mulVec_mem`: an integral matrix maps vectors with
  coordinates of valuation `< 1` (resp. in `𝒪`) to such vectors. The first uses
  `Valuation.map_sum_lt`.
- `integral_entry` and `integral_inv_entry`: the entries of `k` and of `k⁻¹` lie in
  `𝒪` for `k` in the Library's `integralSubgroup 𝒪 m`.

## Determinant orders

For a uniformizing element `ϖ` (hypothesis `hϖ`), `ordDet hϖ g` is
`ord hϖ (det g) : ℤ`, using the Library's `ord`. It is additive (`ordDet_mul`),
`ordDet_one` holds, and `ordDet_eq_zero_of_integral` says it vanishes on
`integralSubgroup`. The last uses the Library's
`Unramified.MinusculeCosets.valuation_det_eq_one`.

## The cell

For `x : GL (Fin (n + 2)) F`:

- `lowGL x : GL (Fin (n + 1)) F` is `low x` when its determinant is a unit, and `1`
  otherwise (a classical `dite`). `lowGL_val` gives its value in the first case.
- `cellVec x = (low x)⁻¹ *ᵥ colT x`.
- `InCell x` means: `det (low x)` is a unit and every coordinate of `cellVec x` has
  valuation `< 1`.

## Left multiplication by matrices with vanishing first-column tail

Let `colT p = 0`. Then:

- `low (p X) = low p * low X` and `colT (p X) = low p *ᵥ colT X`
  (`low_mul_of_colT_eq_zero`, `colT_mul_of_colT_eq_zero`);
- `det p = p₀₀ det (low p)`, and both factors are nonzero
  (`det_eq_of_colT_eq_zero`, `isUnit_of_colT_eq_zero`);
- `cellVec (p x) = cellVec x` and `InCell (p x) ↔ InCell x`
  (`cellVec_mul_of_colT_eq_zero`, `isUnit_det_low_mul_iff`, `inCell_mul_iff`);
- `lowGL (p x) = lowGL p * lowGL x` when `det (low x)` is a unit
  (`lowGL_mul_of_colT_eq_zero`);
- `headUnit hp` is the unit `p₀₀`, and
  `ordDet p = ord p₀₀ + ordDet (lowGL p)` (`ordDet_of_colT_eq_zero`).

Upper-triangular matrices have vanishing first-column tail. These facts let the
Borel subgroup act on the left of the cell.

## Explicit elements

- `colT_lowerUnip`, `low_lowerUnip`, `colT_blockDiag` and `low_blockDiag` give the
  blocks of `L(y)` and `diag(α, h)`. `blockDiag_inv` gives
  `diag(α, h)⁻¹ = diag(α⁻¹, h⁻¹)`.
- `tPrime ϖ = diag(1, ϖ I)`, written `t'`.
- `tPrime_conj_val`:
  `t'⁻¹ x t' = blk x₀₀ (ϖ • rowT x) (ϖ⁻¹ • colT x) (low x)`.
- `tPrime_inv_lowerUnip_tPrime`: `t'⁻¹ L(y) t' = L(ϖ⁻¹ • y)`.
