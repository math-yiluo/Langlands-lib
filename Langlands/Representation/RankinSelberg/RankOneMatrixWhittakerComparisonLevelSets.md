# Finite level-set expansions of locally constant families

This module is a helper for the positive-rank branch (`n = m + 1`) of the
published statement
`Langlands.RankinSelberg.RankOneMatrixWhittakerComparisonStatement`. It imports
only Mathlib and states abstract facts about locally constant functions and
product integrals. It mentions no Whittaker functions, no representations and
no local field.

This is a derived helper, not a statement from the literature. It is intended
for the following step of the positive-rank branch. After the Iwasawa change of
variables, the zeta integral becomes a product integral over `X × Y`. Here `Y`
is a compact group, and the integrand is `H y x * h x`, where `H y` is a model
function translated by `y`. Smoothness makes `y ↦ H y` locally constant. Since
`Y` is compact, `H` then takes finitely many values. The product integral is
therefore a finite sum of single integrals `∫ v x * h x dμ` over the values `v`
of `H`, each weighted by the measure of the set where `H` takes that value. The
module proves this expansion and the matching integrability transfers in the
abstract.

## Topology

Throughout, `Y` is a topological space and `β` is any type.

- `isLocallyConstant_of_mul_right_invariant hU h1 hH`: let `Y` be a group with
  continuous multiplication, and `U` an open set containing `1`. If
  `H (y * u) = H y` for all `y` and all `u ∈ U`, then `H : Y → β` is locally
  constant. Proof: by `IsLocallyConstant.iff_exists_open`, it suffices to give
  for each `y` an open set containing `y` on which `H` equals `H y`. The set is
  the left translate `y U`, which is open by `isOpenMap_mul_left`.
- `finite_range_of_isLocallyConstant hH hC hout`: let `H : Y → β` be locally
  constant and `C ⊆ Y` compact. If `H y = b` for every `y ∉ C`, then
  `Set.range H` is finite. Proof: give `β` the discrete topology. Then `H` is
  continuous (`IsLocallyConstant.continuous`), so `H '' C` is a compact subset
  of a discrete space and hence finite (`IsCompact.finite_of_discrete`). The
  range lies in `H '' C ∪ {b}`.
- `measurableSet_fiber_of_isLocallyConstant hH v`: if `Y` carries a measurable
  structure in which open sets are measurable (`OpensMeasurableSpace Y`), every
  fibre `H ⁻¹' {v}` of a locally constant `H` is measurable. A fibre of a
  locally constant function is open (`IsLocallyConstant.isOpen_fiber`).

## Product integrals

Here `X` and `Y` are measurable spaces with measures `μ` on `X` and `ν` on `Y`.
A family is a function `H : Y → X → ℂ`, so each value `v ∈ Set.range H` is a
function `X → ℂ`. `ν.real s` is the real number `(ν s).toReal`.

- `eq_sum_levelSets hfin y x`: if `Set.range H` is finite, then

  ```text
  H y x = ∑ v ∈ hfin.toFinset, 1_{H⁻¹ v}(y) * v x.
  ```

  Exactly one summand is nonzero, the one with `v = H y`
  (`Finset.sum_eq_single`).
- `levelSet_term_eq_indicator h v`: as functions of `p = (x, y)`,

  ```text
  (v x * h x) * 1_{H⁻¹ v}(y) = 1_{univ × H⁻¹ v}(p) * (H y x * h x).
  ```

  This is checked pointwise, splitting on whether `H y = v`.
- `integral_prod_eq_sum_levelSets hfin hmeas h hint`: let `μ` and `ν` be
  s-finite, `Set.range H` finite, and every fibre `H ⁻¹' {v}` measurable. If
  `(x, y) ↦ H y x * h x` is integrable for `μ.prod ν`, then

  ```text
  ∫ (x, y), H y x * h x ∂(μ.prod ν)
    = ∑ v ∈ hfin.toFinset, ν.real (H⁻¹ v) * ∫ x, v x * h x ∂μ.
  ```

  Proof: expand `H` by `eq_sum_levelSets` and exchange the finite sum with the
  integral (`integral_finsetSum`). Each summand is integrable, because by
  `levelSet_term_eq_indicator` it is the restriction of the integrable integrand
  to the measurable set `univ × H⁻¹ v`. The integral of each summand splits by
  `integral_prod_mul` into `∫ v x * h x dμ` times `∫ 1_{H⁻¹ v} dν`. The second
  factor is `ν.real (H⁻¹ v)` (`integral_indicator`, `setIntegral_const`).
- `integrable_of_integrable_prod_levelSet h hint hv`: let `μ` and `ν` be
  s-finite. Suppose `(x, y) ↦ H y x * h x` is integrable for `μ.prod ν`. If a
  function `v : X → ℂ` has `ν (H⁻¹ v) ≠ 0`, then `x ↦ v x * h x` is integrable
  for `μ`. Proof: for `ν`-almost every `y`, the section `x ↦ H y x * h x` is
  integrable (`Integrable.prod_left_ae`). A set of positive measure contains a
  point where an almost-everywhere property holds
  (`Measure.exists_mem_of_measure_ne_zero_of_ae`). At such a point
  `H y = v`.
- `integrable_prod_of_levelSets hfin hmeas h hv`: let `ν` be s-finite,
  `Set.range H` finite, and every fibre measurable. Suppose every nonzero value
  `v` of `H` has `ν (H⁻¹ v) ≠ ∞` and `x ↦ v x * h x` integrable for `μ`. Then
  `(x, y) ↦ H y x * h x` is integrable for `μ.prod ν`. Proof: rewrite the
  integrand as the finite sum from `eq_sum_levelSets` and apply
  `integrable_finsetSum`. The summand for `v = 0` is zero. For any other value,
  the summand is the product of `x ↦ v x * h x` and the indicator of a set of
  finite `ν`-measure. Such a product is integrable for `μ.prod ν`
  (`Integrable.mul_prod`).
