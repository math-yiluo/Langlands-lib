# The end ring is a henselian discrete valuation ring

Module `Langlands.Correspondence.Laumon.EndRingDvr`. It works with the ring `endRing k` of the
module `Langlands.Correspondence.Laumon.Traits`: the elements of `endField k`, the separable
closure of `k(t)` in `k((t))`, that are power series. `endPowerSeriesHom k : endRing k → k⟦t⟧`
recovers the power series of an element.

## The embedding into power series

- `ofPowerSeries_endPowerSeriesHom`, `endPowerSeriesHom_eq_iff`: the power series of `x`, viewed
  as a Laurent series, is `x`.
- `endPowerSeriesHom_injective`; `mem_endRing_iff` restates the definition of `endRing k`.
- `endPowerSeriesHom_endUniformizer` (`t ↦ X`), `endPowerSeriesHom_endConstantHom` (constants),
  `endPowerSeriesHom_comp_endChartCoordinate`, `endPowerSeriesHom_endChartCoordinate`: the chart
  coordinate `k[x] → endRing k`, `x ↦ t`, followed by the power series map is the inclusion
  `k[x] → k⟦X⟧`.
- `endResidue_apply`: the residue map is the constant coefficient.
- `algebraMap_comp_subtype_endRing`, `aeval_map_subtype_endRing`: evaluating a polynomial over
  `endRing k` at a power series inside `k((t))` is evaluating its image over `k⟦t⟧`.

## Units, divisibility, factorization

- `isUnit_endRing_iff`: `x` is a unit of `endRing k` if and only if its constant coefficient is
  nonzero. If it is, the power series inverse of `x` is the Laurent series of `x⁻¹ ∈ endField k`,
  so `x⁻¹ ∈ endRing k`.
- `endRing_dvd_iff`: `x ∣ y` in `endRing k` if and only if the power series of `x` divides that
  of `y`; the quotient `y / x` is computed in the field `endField k`.
- `exists_eq_endUniformizer_pow_mul`: every nonzero `x` is `t ^ n v` with `v` a unit, `n` the
  order of its power series (Mathlib's `PowerSeries.X_pow_order_mul_divXPowOrder`).
- `irreducible_endUniformizer`: `t` is irreducible; if `t = a b` with `a, b` nonunits, both power
  series are divisible by `X`, and `X² ∣ X` is false.
- `isDiscreteValuationRing_endRing` (instance): with these facts, Mathlib's
  `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization` shows that `endRing k` is a
  discrete valuation ring with uniformizer `t`.
- `mem_maximalIdeal_endRing_iff`, `mem_maximalIdeal_powerSeries_iff`: the maximal ideals are the
  elements with zero constant coefficient.

## Henselian

`henselianLocalRing_endRing` (instance): `endRing k` is a henselian local ring. Let `f` be monic
over `endRing k` with `f(a₀) ∈ 𝔪` and `f'(a₀)` a unit. Its image over `k⟦t⟧`, which is henselian
(`Langlands.CommutativeAlgebra.powerSeries_henselianLocalRing`), has a root `α ≡ a₀`, and
`f'(α)` is a unit, so `α` is a simple root of `f` over `endField k` inside `k((t))`. Hence the
derivative of the minimal polynomial of `α` over `endField k` is nonzero, so `α` is separable
over `endField k`. Since the separable closure of `k(t)` in `k((t))` is separably closed there
(Mathlib's `separableClosure.separableClosure_eq_bot`), `α ∈ endField k`, and as a power series
`α ∈ endRing k`; it is a root of `f` congruent to `a₀`.

These are the first three conjuncts of `EndTraitHenselizationStatement`.

Provenance: internal; the arguments are standard (the `t`-adic valuation on the separable
closure of `k(t)` in `k((t))`, and Hensel's lemma in `k⟦t⟧`).
