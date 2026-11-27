# Proof of ordinary nonvanishing for unequal ranks at a real place

Module `Langlands.Global.RankinSelberg.RealUnequalOrdinaryPlaceTestsProof`, namespace
`Langlands.Global.RankinSelbergGlobal`. The main theorem is

```
theorem realUnequalOrdinaryPlaceTests : RealUnequalOrdinaryPlaceTestsStatement.{u}
```

proving the Library statement `RealUnequalOrdinaryPlaceTestsStatement` (module
`UnequalPlaceTestsFromOrdinary`) with the field universe `u` free. It uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## The statement

For a number field `F` with compact adelic quotient, a unitary additive character `ψ` of the adeles
trivial on `F`, `t < r`, actual cuspidal realizations `T` of `GL_(r+1)` and `T'` of `GL_(t+1)`, a real
place `v` with component scale `a` of `ψ`, and real-place parameters `d`, `d'` of `T` and `T'`, there
are actual real-place Whittaker restrictions `W` of `T` for `ψ` and `W'` of `T'` for `ψ⁻¹`, and
compatible quotient measure data `D` on `N_(t+1) \ GL_(t+1)(ℝ)`, such that the ordinary integral
`realUnequalIntegral h D W W' s` is nonzero at some `s` with `Re s > σ`, for every `σ`.

`realUnequalOrdinaryPlaceTest` proves this for each such datum, with `D = realQuotientMeasureData t`;
`realUnequalOrdinaryPlaceTests` packages it.

## Proof of `realUnequalOrdinaryPlaceTest`

1. **Actual vectors.** The real branch of `archimedeanActualWhittakerIntertwiners` gives a real
   Whittaker intertwiner `B` on the compact-finite standard module of `d` whose values `B f` are actual
   restrictions of `T` for `ψ` (finite coordinate one), and a vector `f` with `B f 1 = 1`. The right
   derivative `fX` of `f` along `E₀₁` (`firstRootDirection`) is again compact-finite and
   `B fX = R(E₀₁)(B f)` (derivative clause of `IsRealWhittakerIntertwiner`).
   `cuspidalWhittakerIdentityNonzero` for `ψ⁻¹` gives an actual restriction `W'` of `T'` with
   `W'(1) ≠ 0`. By `realPlaceUniformWhittakerModel` and `realUniformWhittakerRegularity`, `W'` lies
   in `realUniformWhittakerModel t d' (-a)`, has the left character of `-a`, is continuous, and every
   `B g` and `W'` satisfy the simple-root gauge bound `HasGaugeBound` (`hasGaugeBound_of_mem_model`).
2. **Contradiction hypothesis.** Suppose the conclusion fails. Then for every compact-finite `g` the
   ordinary integral of `B g` against `W'` (for `realQuotientMeasureData t`) vanishes on a right
   half-plane.
3. **Descent to `GL₁`** (`RealUnequalPositiveRank.descent_to_rankZero`). Write `V_k` for the
   restriction `z ↦ W'(diag(z, 1))` of `W'` to `GL_(k+1)(ℝ)`, `k ≤ t`. By induction on `t - k`, for
   every `g` the ordinary integral of `B g` against `V_k` for `realQuotientMeasureData k` vanishes on a
   right half-plane. For `k = t`, `V_t = W'` (`padGL_refl`). From `k + 1` to `k`:
   - `V_(k+1)` has the left character of `-a` (`hasLeftCharacter_padGL`, from the Library's
     `realWhittakerCharacter_padGL`), is continuous, and has a gauge bound (`hasGaugeBound_padGL`, from
     `hasGaugeBound_pad` of module `RealUnequalLastRowDescent`);
   - **genuine right translates** (`translate_vanishing_of_intertwiner`): the ordinary integral of every
     right translate `x ↦ B g (x c)` against `V_(k+1)` vanishes on a right half-plane. Write
     `Ψ(s; κ)` for the ordinary integral of `x ↦ B g (x κ c)` against `V_(k+1)`, `κ ∈ O(r+1)`. For a
     polynomial weight `w` on `O(r+1)` (`polynomialStar`), the Library's compact projection
     `realWhittakerTranslateProjection` (module `RealWhittakerTranslateProjection`, through
     `exists_polynomial_projection`; the finite span of left translates is
     `polynomial_finiteLeftSpan`) writes the average `x ↦ ∫ w(κ) B g (x κ c) dκ` as some `B p`, whose
     integral vanishes on a right half-plane. The translates `x ↦ B g (x κ c)` form a compact family
     with a uniform gauge (the Library's `compact_rightTranslate_uniformGauge`), so
     `ordinary_halfPlaneDomination` gives majorants uniform in `κ`. By Fubini (`integrand_average`)
     the integral of `B p` is `∫ w(κ) Ψ(s; κ) dκ`; it is holomorphic on the common half-plane, so it
     vanishes there (`eq_zero_on_right`). Since `κ ↦ Ψ(s; κ)` is continuous and its integrals against
     all polynomial weights vanish, the Library's `eq_zero_of_integral_polynomial_mul_eq_zero` gives
     `Ψ(s; κ) = 0` for all `κ`, in particular at `κ = 1` (`translate_vanishing`);
   - **last row**: applied with the column unipotents `colUnip y`, the descent theorem
     `lastRow_descent` (`RealUnequalLastRowDescentStatement`) gives vanishing of the integral of `B g`
     against `z ↦ V_(k+1)(diag(z, 1))`, which is `V_k` by the Library's `padGL_padGL`.
4. **Rank zero.** For `k = 0`, the ordinary integrals of `B f` and of `B fX = R(E₀₁)(B f)` against
   `V₀` vanish on right half-planes, and both integrands are integrable on a right half-plane
   (`exists_integrable`, from `ordinary_halfPlaneDomination`). The Mellin argument
   `RealUnequalRankZero.value_eq_zero_of_integrals_eq_zero` (module `RealUnequalRankZeroOrdinary`)
   gives `B f (1) · V₀(1) = 0`. But `B f (1) = 1` and `V₀(1) = W'(1) ≠ 0`, a contradiction.

## Provenance

The statement is the Library's. The route is internal and follows the structure of H. Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §6.2, Propositions 6.1–6.2, pp. 41–42 of the
author-posted version (`jacquet-2009-archimedean-rankin-selberg`): multiplication of the restriction of
a Whittaker function to the smaller group by functions of the last row, obtained from right translates
by upper column unipotent elements, is used to separate the last row one step at a time. Since only
compact-finite actual vectors are available, genuine right translates are reached through compact
projections (`RealWhittakerTranslateProjection`) and polynomial density on `O(r+1)`, and the final step
on `GL₁` uses the Mellin inversion of `RealUnequalRankZeroOrdinary`.
