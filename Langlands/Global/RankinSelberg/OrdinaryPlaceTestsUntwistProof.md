# Proof: untwisting the ordinary archimedean tests from the split centre

Module `Langlands.Global.RankinSelberg.OrdinaryPlaceTestsUntwistProof`, namespace
`Langlands.Global.RankinSelbergGlobal`. The theorem

```lean
theorem ordinaryPlaceTestsUntwist : OrdinaryPlaceTestsUntwistStatement.{u}
```

proves the statement `OrdinaryPlaceTestsUntwistStatement` of the module
[`ArchimedeanOrdinaryTestsSplitCentre`](ArchimedeanOrdinaryTestsSplitCentre.md): the conjunction
of the four implications

- `RealUnequalOrdinaryPlaceTestsSplitCentreStatement → RealUnequalOrdinaryPlaceTestsStatement`
  (`realUnequalOrdinaryPlaceTests_of_splitCentre`),
- `ComplexUnequalOrdinaryPlaceTestsSplitCentreStatement → ComplexUnequalOrdinaryPlaceTestsStatement`
  (`complexUnequalOrdinaryPlaceTests_of_splitCentre`),
- `RealEqualOrdinaryPlaceTestsSplitCentreStatement → RealEqualOrdinaryPlaceTestsPositiveRankStatement`
  (`realEqualOrdinaryPlaceTests_of_splitCentre`),
- `ComplexEqualOrdinaryPlaceTestsSplitCentreStatement →
  ComplexEqualOrdinaryPlaceTestsPositiveRankStatement`
  (`complexEqualOrdinaryPlaceTests_of_splitCentre`).

Each restricted statement is the unrestricted one for cuspidal realizations `T`, `T'` with the
extra hypotheses `IsTrivialOnSplitCentre T` and `IsTrivialOnSplitCentre T'`. The proof follows
the route described in the Markdown of the statement's module, section "Why the untwisting
premise holds". It uses the helper modules `RealStandardComplexTwist` and
`RealPlaceParameterNormPowerTwist`.

## The four implications

All four proofs have the same shape. Fix the data of the unrestricted statement: `F`, `ψ`
trivial on `F`, realizations `T`, `T'`, a place, the scale `a` of `ψ` there, and parameter lists
`d`, `d'` of `T`, `T'` at that place.

1. **Twist to the split centre.** The published
   `NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre` gives complex `λ`, `λ'` such
   that `T₁ = T.heckeDeterminantTwist (HeckeCharacter.normPower F (-λ))` and the analogous
   twist `T₁'` of `T'` are trivial on the split centre.
2. **Parameters of the twists.** At a real place `v`,
   `CuspidalOperatorRealization.hasRealPlaceParameter_heckeDeterminantTwist_normPower` (module
   `RealPlaceParameterNormPowerTwist`) shows that `T₁` has the parameter
   `d.map (realBlockComplexTwist (-λ))`. At a complex place `w`, the published
   `ComplexPlaceHeckeTwist.exists_hasComplexPlaceParameter` gives a parameter `e` of
   `‖·‖^(-λ)` at `w`, and the published
   `OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist_mul` shows that `T₁` has
   the parameter `d.map (·.mul e)`. The same holds for `T₁'`.
3. **Apply the restricted statement** to `T₁`, `T₁'`, the same place, scale and `ψ`, and these
   parameter lists. It returns restrictions `W`, `W'` of global Whittaker functions of `T₁`
   (for `ψ`) and `T₁'` (for `ψ⁻¹`), quotient measure data `D`, in equal rank a Schwartz function
   `Φ`, and nonvanishing of the ordinary integral of `(W, W')` at points arbitrarily far to the
   right.
4. **Untwist the restrictions.** `isRealPlaceWhittaker_of_heckeDeterminantTwist_normPower`
   (resp. the complex version) writes `W = c |det|^(-λ) W₀` with `c ≠ 0` and `W₀` an actual
   restriction of `T` at the same place and finite point, and likewise
   `W' = c' |det|^(-λ') W₀'`. Here `|det|^z` is `ArchimedeanLocal.detPower nabs g z` for the
   normalized absolute value `nabs` of the place (`realNormalizedAbs`,
   `complexNormalizedAbs`).
5. **Shift the spectral variable.** `ArchimedeanLocal.unequalIntegral_detPower_mul` and
   `ArchimedeanLocal.equalIntegral_detPower_mul` give
   `Ψ(s; c |det|^(-λ) W₀, c' |det|^(-λ') W₀') = c c' Ψ(s - λ - λ'; W₀, W₀')`, in unequal rank and
   (with the same `Φ`) in equal rank, for the same measure `D`.
   `exists_re_gt_ne_zero_of_eq_mul_shift` transfers nonvanishing at points arbitrarily far to
   the right from the left side to `Ψ(·; W₀, W₀')`: given `σ`, take a point `s` with
   `Re s > σ + Re(λ + λ')` where the left side is nonzero, and use `s - λ - λ'`.

The final witnesses are `W₀`, `W₀'`, `D` and, in equal rank, `Φ`.

## Supporting results in this module

- `ArchimedeanLocal.detPower_add`: `|det g|^(s + t) = |det g|^s |det g|^t`.
  `ArchimedeanLocal.detPower_padGL`: `|det diag(g, 1)|^s = |det g|^s`, by the published
  `UnequalAnalytic.det_padGL`.
- `ArchimedeanLocal.unequalIntegral_detPower_mul`, `ArchimedeanLocal.equalIntegral_detPower_mul`:
  for every normalized absolute value `nabs` and quotient measure, multiplying the two
  functions by `c |det|^a` and `c' |det|^b` multiplies the integral by `c c'` and replaces `s` by
  `s + (a + b)`. The integrands agree pointwise after `detPower_padGL` and `detPower_add`, and
  `MeasureTheory.integral_const_mul` pulls out the constant; no integrability is needed.
- `cuspWhittaker_heckeDeterminantTwist`: for every Hecke character `ν`, the global Whittaker
  function of the twisted vector `T.realization.heckeDeterminantTwistEquiv ν x` at an adelic point
  `p` is `ν(det p)` times that of `x`. The twisted function is `ν(det) · φ_x`
  (`evaluate_heckeDeterminantTwistEquiv`), and `ν(det(u p)) = ν(det p)` for `u` in the upper
  unitriangular adelic group, whose determinant is `1`
  (`Unfolding.isUnitriangular_of_mem_unipotentAdelic`). The constant leaves the Whittaker
  integral.
- `normPower_adelicDeterminant_adelicEquiv`: `‖·‖^s ∘ det` at an adelic point `p` is
  `exp (s log ‖det p‖)` with `‖det p‖ = detNorm F n p`.
- `isRealPlaceWhittaker_of_heckeDeterminantTwist_normPower`: if
  `W(g) = W_y(ι_v(g) a)` for a vector `y` of the twist by `‖·‖^(-λ)` and a finite adelic point
  `a`, write `y` as the twist of a vector `x` of `T`. Then
  `W(g) = c |det g|^(-λ) W_x(ι_v(g) a)` with `c = exp(-λ log ‖det a‖) ≠ 0`, because
  `‖det(ι_v(g) a)‖ = |det g| ‖det a‖` (`Unfolding.detNorm_mul`,
  `RealPlaceRestriction.detNorm_realPlacePoint`).
  `isComplexPlaceWhittaker_of_heckeDeterminantTwist_normPower` is the same at a complex place
  `w`, with `‖det(ι_w(g))‖ = ‖det g‖²` (`ComplexPlaceAnalytic.detNorm_complexPlacePoint`), the
  normalized absolute value of `det g` at `w`.

The proofs use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

The statement's Markdown gives the provenance: the archimedean local tests of J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), proof of Theorem 4.1, printed pp. 219–220, and
the normalization by a norm power of H. Jacquet and J. A. Shalika, *On Euler products and the
classification of automorphic forms II*, Theorem 4.2, printed pp. 806–807. The proof here is the
Library's own argument through the results named above.
