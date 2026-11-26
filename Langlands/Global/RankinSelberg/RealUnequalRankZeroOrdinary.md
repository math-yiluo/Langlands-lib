# Ordinary nonvanishing at a real place when the smaller group is GL₁

Module `Langlands.Global.RankinSelberg.RealUnequalRankZeroOrdinary`, namespace
`Langlands.Global.RankinSelbergGlobal`. The module proves the case `t = 0` of
`RealUnequalOrdinaryPlaceTestsStatement` (module `UnequalPlaceTestsFromOrdinary`), in which the
smaller group is `GL₁(ℝ)`. It states the remaining cases `0 < t` as a separate proposition and
proves that they imply the full statement. It does not prove the cases `0 < t`.

## Statements

- `RealUnequalOrdinaryPlaceTestsPositiveRankStatement.{u}` is
  `RealUnequalOrdinaryPlaceTestsStatement.{u}` with the extra hypothesis `0 < t` after
  `h : t < r`. All other quantifiers and the conclusion are unchanged. The conclusion asks for
  actual real-place restrictions `W` of `T` for `ψ` and `W'` of `T'` for `ψ⁻¹`, and for one
  compatible quotient measure `D` on `N_(t+1)(ℝ) \ GL_(t+1)(ℝ)`. With these fixed, the ordinary
  integral `realUnequalIntegral h D W W'` must be nonzero somewhere in every right half-plane.
- `RealUnequalOrdinaryPlaceTestsFromPositiveRankStatement.{u}` is the implication
  `RealUnequalOrdinaryPlaceTestsPositiveRankStatement.{u} → RealUnequalOrdinaryPlaceTestsStatement.{u}`.
  `realUnequalOrdinaryPlaceTestsFromPositiveRank` proves it. When `t = 0` it applies the theorem
  below. When `0 < t` it applies the premise.

## The case `t = 0`

`realUnequalOrdinaryPlaceTest_rankZero` takes the data of `RealUnequalOrdinaryPlaceTestsStatement`
with `t = 0` and `h : 0 < r`. These are a number field `F` with compact adelic quotient, a unitary
adelic additive character `ψ` trivial on `F`, cuspidal realizations `T` of `GL_(r+1)` and `T'` of
`GL₁`, a real place `v`, a scale `a` with `IsRealAdditiveComponent ψ v a`, and real-place
parameters `d`, `d'`. It gives actual restrictions `W`, `W'` and quotient measure data `D` as in
that statement. The measure is always `realQuotientMeasureData 0`.

### Proof

1. **The two tests.** `archimedeanActualWhittakerIntertwiners` gives a Whittaker intertwiner `B`
   on the compact-finite standard module of `d`, with `B f g` the global Whittaker function of an
   actual vector at `realPlacePoint g`, and a source vector `f` with `B f 1 = 1`. Let `X` be the
   matrix unit `E₀₁` (`firstRootDirection`). The right derivative `R(X) f` is again
   compact-finite (`rightDerivative_mem_kFiniteFunctions_realStandardModule`), and the derivative
   clause of `IsRealWhittakerIntertwiner` gives `B (R(X) f) = R(X) (B f)`. So `B f` and
   `R(X)(B f)` are both actual restrictions with finite coordinate one. For `T'`,
   `cuspidalWhittakerIdentityNonzero` for `ψ⁻¹` (standard by `isStandardAdditiveCharacter_of_unitary`
   applied to `inverseCharacter ψ`) gives a vector `x'` whose Whittaker function is nonzero at the
   identity. `W'` is its restriction with finite coordinate one, so `W'(1) ≠ 0`.
2. **Convergence.** `realPlaceUniformWhittakerModel` places both larger restrictions in
   `realUniformWhittakerModel r d a` and `W'` in `realUniformWhittakerModel 0 d' (-a)`.
   `realUniformWhittakerRegularity` and `realUnequalPairConvergence` then give a common right
   half-plane where both ordinary integrands are integrable.
3. **The modulation.** Suppose both ordinary integrals vanish on right half-planes. For
   `g ∈ GL₁(ℝ)`, `pad_mul_firstRoot` moves the transvection `1 + zE₀₁` to the left of
   `diag(g, 1, …, 1)` and multiplies its parameter by `det g`. Left equivariance and
   `character_firstRoot` give `W(diag(g,1)(1 + zE₀₁)) = e(a · det g · z) W(diag(g,1))`, where
   `e(x) = exp(2πix)` is `Real.fourierChar`. Differentiating at `z = 0` along the curve `1 + zE₀₁`
   (`rightDerivative_eq_fderiv_mul_left`) gives `rightDerivative_firstRoot_pad`:
   `(R(X)W)(diag(g,1)) = 2πi a det g · W(diag(g,1))`.
4. **The line.** `lineProduct h W W' x` is `W(diag(x,1)) W'(x)` for `x ≠ 0` and `0` at `0`.
   `RealRankZero.exists_measure_eq` writes the quotient measure as `κ |x|⁻¹ dx` with `κ ≠ 0`. With
   `unitsExtend_integrand`, `integral_eq_weighted` and `integral_eq_integral_Ioi_add_neg`, the
   ordinary integral at `s` is `κ` times the Mellin transform at `s - r/2` of the even part
   `E(t) = L(t) + L(-t)`, where `L = lineProduct h W W'` and `t > 0` (`weighted_add_neg`). By
   `lineProduct_rightDerivative` and `weighted_add_neg_rightDerivative`, the integral for
   `R(X)W` at `s` is `2πi a κ` times the Mellin transform at `s - r/2 + 1` of the odd part
   `O(t) = L(t) - L(-t)`. Integrability on the convergence half-plane gives Mellin convergence of
   `E` and `O` on vertical lines far enough to the right.
5. **Inversion.** On such a line both Mellin transforms vanish. `eq_zero_of_mellin_eq_zero`
   applies Mathlib's `mellinInv_mellin_eq` at `1`. Continuity of `L` at `±1`
   (`continuousAt_lineProduct`) gives `E(1) = O(1) = 0`, so `L(1) = 0`. By `lineProduct_one`
   this is `W(1) W'(1) = 0` (`value_eq_zero_of_integrals_eq_zero`). But `W(1) = B f 1 = 1` and
   `W'(1) ≠ 0`. So one of the two tests is nonzero somewhere in every right half-plane, and that
   test is the witness.

## Helper declarations

The namespace `Langlands.Global.RankinSelbergGlobal.RealUnequalRankZero` contains the following.

- `integral_eq_integral_Ioi_add_neg`: `∫ φ = ∫_(0,∞) (φ(t) + φ(-t)) dt` for integrable `φ` on `ℝ`.
- `eq_zero_of_mellin_eq_zero`: if `f` is Mellin convergent at `σ`, its Mellin transform vanishes
  on the line `Re = σ`, and `f` is continuous at `1`, then `f(1) = 0`.
- `firstRoot h z` is the upper unipotent matrix `1 + z E₀₁`. `firstRootDirection h` is `E₀₁`.
  `firstRoot_val_coe`, `character_firstRoot` and `pad_mul_firstRoot` are the matrix and
  character identities used in step 3.
- `hasDerivAt_fourierChar_mul`: the derivative of `z ↦ e(cz)` at `0` is `2πic`.
- `pairProduct` is the spectral-free product on the quotient and `lineProduct` is its
  extension by zero to `ℝ`. `weighted h W W' s` is the extension by zero of the full ordinary
  integrand `realUnequalIntegrand h W W' s` multiplied by `|x|⁻¹`; for `x ≠ 0` it equals
  `lineProduct h W W' x · |x|^(s - r/2 - 1)`, the absolute value taken in `ℝ` before casting.
  For a compatible quotient measure `κ |x|⁻¹ dx`, the ordinary integral is `κ` times the
  Lebesgue integral of `weighted` (`integral_eq_weighted`). `lineProduct_units`,
  `lineProduct_zero`, `lineProduct_one`, `unitsExtend_integrand`,
  `lineProduct_rightDerivative` and `continuousAt_lineProduct` evaluate them.
- `cpow_sub_one_of_pos`, `weighted_add_neg`, `weighted_add_neg_rightDerivative`,
  `integrable_weighted` and `integral_eq_weighted` give the Mellin identities of step 4.
- `value_eq_zero_of_integrals_eq_zero` is steps 3–5 for any smooth `W` with the left character
  of `a` and any continuous `W'`, given integrability on a common right half-plane.
- `adelicPoint_one`, `InfiniteWhittakerSlice.finitePoint_one`, `realPlacePoint_one` and `mul_finitePoint_one` evaluate
  the adelic points at the identity.

## Provenance

This is an internal result. The modulation in step 3 is the infinitesimal form of the last-row
phase in H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §6.2, proof of
Proposition 6.1, author pp. 41–42 (`jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`). There, a right translate by
an upper column unipotent element multiplies the restriction to `diag(g, 1)` by the character of
the last row of `g`. The actual restrictions here are compact-finite, so the module uses the
Lie derivative along `E₀₁` instead of the translate. It multiplies by `2πi a x`. With smaller
group `GL₁`, the Mellin transform in the spectral variable and the parity of this factor replace
Jacquet's Fourier localization in the last row. The general existence of tests is Jacquet 2009,
Theorems 2.3 and 2.6, author pp. 8–10.
