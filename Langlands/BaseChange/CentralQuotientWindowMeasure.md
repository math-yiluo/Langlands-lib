# A Haar measure on `GL_n(F)` modulo its center from a determinant window

Lean module: `Langlands.BaseChange.CentralQuotientWindowMeasure`.

Let `F` be a nonarchimedean local field, `n > 0`, `G = GL_n(F)` and `Z` its center. The module
builds a Haar measure on `G ⧸ Z` directly from a Haar measure `μ` of `G`: restrict `μ` to the
determinant window

`D = { g : 0 ≤ ord_F(det g) < n }`

and push it forward to `G ⧸ Z`. The window meets each orbit of left multiplication by the
powers of the scalar `ϖ` (a uniformizer) exactly once, because `ord_F(det(ϖ g)) = n + ord_F(det g)`,
and the remaining part `Z ∩ D` of the center is the compact group of scalar units. This is the usual
description of the quotient measure through a fundamental domain; the module proves what the
rest of the Library uses of it.

## Degree windows (any group)

For a homomorphism `w : H →* Multiplicative ℤ`, `degreeWindow w n c` is the set of `h` with
`c ≤ w h < c + n` (degrees written additively).

- `degreeWindow_mul_left`: the preimage of a window under left multiplication by `a` is the
  window shifted by `-w a`.
- `isFundamentalDomain_degreeWindow`: if `w s = n > 0` and the window is measurable, it is a
  fundamental domain for left multiplication by `Subgroup.zpowers s`, for every measure. The
  proof uses `existsUnique_add_zsmul_mem_Ico`: each degree has exactly one shift by a multiple of
  `n` into `[c, c + n)`.
- `measure_inter_degreeWindow_eq`: for a left-invariant measure and a measurable set `A` stable
  under left multiplication by the powers of `s`, all windows cut the same measure out of `A`
  (`IsFundamentalDomain.measure_set_eq`).

## The determinant order on `GL_n(F)`

- `isCompact_unitGroup`: the units of the valuation ring form a compact subset of `Fˣ`; it is the
  preimage in `Fˣ` of the closed sphere `{x : v x = 1}`, which lies in the compact closed unit ball,
  under the embedding `Units.val` (`Units.isEmbedding_val₀`).
- `determinantOrder F n : GL_n(F) →* Multiplicative ℤ` is `g ↦ ord_F(det g)`, the composite of
  `GeneralLinear.determinant` with `fieldOrderUnits F`. It is continuous into the discrete group
  `ℤ` (`continuous_determinantOrder_toAdd`), so every window is open
  (`isOpen_degreeWindow_determinantOrder`), and `determinantOrder_scalar_mul` gives
  `ord(det(a g)) = n · ord(a) + ord(det g)` for a scalar `a`.
- `scalar_mem_center`, `exists_scalar_of_mem_center` (from
  `Matrix.GeneralLinearGroup.center_eq_range_scalar`) and `mk_scalar_mul`: the center consists of
  the scalar matrices, which act trivially on `G ⧸ Z`.
- `exists_isCompact_scalar_of_mem_window`: for a compact `K ⊆ G` there is a compact set `B` of
  units such that `a k ∈ D` with `k ∈ K` forces `a ∈ B`. The degrees of `K` are bounded by some
  `M`, so `ord(a)` lies in `[-(M + n), M + n]`, and `B` is the finite union of the compact sets
  `ϖ^j · O_F^×` for `j` in that range.

## The window measure

`windowMeasure F n μ = (μ.restrict D).map QuotientGroup.mk`, a measure on `G ⧸ Z` with
`windowMeasure_apply`: `windowMeasure F n μ A = μ (mk⁻¹(A) ∩ D)` for measurable `A`.

- `windowMeasure_isMulLeftInvariant`: if `μ` is left invariant, so is the window measure. For a
  class `gZ` and a measurable `A`, the set `mk⁻¹(A)` is stable under the scalar `ϖ`, and `D` is
  the preimage under left multiplication by `g` of the window starting at `ord(det g)` (by
  `degreeWindow_mul_left`, the preimage of `D` itself starts at `-ord(det g)`). After
  translating by `g`, the measures agree by `measure_inter_degreeWindow_eq` with `s = ϖ`.
- `windowMeasure_isHaarMeasure`: if `μ` is a Haar measure on `G`, the window measure is a Haar
  measure on `G ⧸ Z`. The test set is the image of a compact open subgroup `K₀` of `G`
  (`LocalFieldTopology.generalLinear_compactOpen`). Its window measure is positive because
  `K₀ ∩ D` is an open neighbourhood of `1`. It is finite because `mk⁻¹(mk K₀) ∩ D` lies in the
  compact set `B · K₀` given by `exists_isCompact_scalar_of_mem_window`.

All results here are standard facts about quotient measures and fundamental domains,
specialized to `GL_n(F)` and the window `D`.
