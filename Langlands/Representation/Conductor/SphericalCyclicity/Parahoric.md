# The parahoric subgroup of type `(1, n + 1)` and right multiplication on the cell

Author: Worker 392.

This helper module of the proof of
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` (see
[`OrderedUnramifiedSphericalCyclicity`](../OrderedUnramifiedSphericalCyclicity.md))
works over `F` with `ValuativeRel F` and a uniformizing element `ϖ`
(`hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ`). Write `v`,
`𝒪`, `K = integralSubgroup 𝒪 (n + 1)` and `t' = tPrime ϖ` as in [`Cells`](Cells.md).
The definitions are internal auxiliary constructions, with no literature source.
All declarations are in `Langlands.Conductor.SphericalCyclicity`.

## Valuations and congruence levels

- `val_lt_one_iff_le_uniformizer`: `v x < 1 ↔ v x ≤ v ϖ`, because the value group
  is discrete. `val_inv_uniformizer_mul_le_one` and
  `val_lt_one_of_inv_uniformizer_mul_le_one` give `v x < 1 ↔ v (ϖ⁻¹ x) ≤ 1`.
- `mem_maximalIdeal_pow_iff`: `x ∈ 𝔪^a ↔ v x ≤ (v ϖ)^a`, for `x : 𝒪`. It uses the
  Library's `maximalIdeal_pow_eq_span_jacquetUniformizer` and divisibility in the
  valuation integers.
- `val_uniformizer_pow_le_one`: `(v ϖ)^a ≤ 1`.
- `mem_principalLevelSubgroup_iff`: `g` lies in the Library's
  `principalLevelSubgroup F m a` if and only if every entry of `g - 1` and of
  `g⁻¹ - 1` has valuation at most `(v ϖ)^a`. It is derived from the Library's
  `mem_principalCongruenceSubgroup_iff` and the previous item.
- `val_det_sub_head_mul_lt`: if `X` is integral and `v (colT X i) < 1` for all `i`,
  then `v (det X - X₀₀ det (low X)) < 1`. The proof expands along column zero: every
  term other than the first contains a factor `X (i+1) 0` of valuation `< 1`
  (`Valuation.map_sum_lt`; `val_neg_one_pow_mul` removes the signs).

## The parahoric subgroup

`parahoric ϖ = K ⊓ K.comap (conj t'⁻¹)`. This is the subgroup `J = K ∩ t' K t'⁻¹`.

- `integral_tPrime_conj_iff` and `mem_parahoric_iff`:
  `x ∈ J ↔ x ∈ K ∧ ∀ i, v (colT x i) < 1`. By `tPrime_conj_val`, `t'⁻¹ x t'` has
  blocks `x₀₀`, `ϖ • rowT x`, `ϖ⁻¹ • colT x` and `low x`. Its entries are integral
  exactly when `v (colT x i) < 1`. Its determinant equals `det x`, so the Library's
  `Unramified.MinusculeCosets.mem_integralSubgroup_of_det` applies.
- `parahoric_head`: for `u ∈ J`, `v u₀₀ = 1` and `v (det (low u)) = 1`. Indeed
  `v (det u) = 1`, and `det u ≡ u₀₀ det (low u)` modulo the maximal ideal
  (`val_det_sub_head_mul_lt`, `Valuation.map_eq_of_sub_lt`), so the product has
  valuation one. Both factors are integral (`val_eq_one_of_mul_eq_one`).
- `isUnit_det_low_of_parahoric`, `lowGL_mem_integral_of_parahoric`
  (`lowGL u ∈ integralSubgroup 𝒪 n`), `inCell_of_parahoric` (`InCell u`), and
  `lowerUnip_mem_parahoric` (`L(y) ∈ J` when every `v (y i) < 1`).

## Right multiplication on the cell

- `low_mul_lowerUnip`: `low (X L(y)) = low X`.
- `colT_mul_lowerUnip_neg_cellVec`: `colT (x L(-cellVec x)) = 0`, and
  `lowGL_mul_lowerUnip_neg_cellVec`: `lowGL (x L(-cellVec x)) = lowGL x`.
- `cell_mul_parahoric`: if `InCell x` and `k ∈ J`, then `InCell (x k)`,
  `L(cellVec x) k ∈ J` and `lowGL (x k) = lowGL x * lowGL (L(cellVec x) k)`. Proof:
  set `y = cellVec x` and `p = x L(-y)`. Then `colT p = 0` and
  `x k = p (L(y) k)` with `L(y) k ∈ J`. The left-multiplication lemmas of
  [`Cells`](Cells.md) apply.
- `inCell_of_mul_parahoric` and `inCell_mul_parahoric_iff`:
  `InCell (x k) ↔ InCell x` for `k ∈ J`.

## Principal congruence elements

- `integral_of_mem_principalLevel`: `K_a ⊆ K`.
- `mem_parahoric_of_principalLevel`: `K_a ⊆ J` for `a > 0`.
- `one_succ_succ`: the identity matrix restricted to the lower-right block is the
  identity.
- `lowGL_lowerUnip_mul_mem_principalLevel`: if `a > 0`, every `v (y i) < 1` and
  `k ∈ K_a`, then `H = lowGL (L(y) k)` lies in the principal congruence subgroup of
  level `a` of `GL_(n+1)`. Here `H = y ⊗ rowT k + low k`, so each entry of `H - 1` is
  `y_i (k_{0,j+1} - 0) + (k_{i+1,j+1} - δ_ij)`, which has valuation at most
  `(v ϖ)^a`. For the inverse, `H⁻¹ - 1 = H⁻¹ (1 - H)`, where `H⁻¹` is integral.
