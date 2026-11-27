# Proof of the uniform temperedness criterion on Siegel sets

Module `Langlands.Global.AdelicUniformTemperednessCriterionProof`.

## Main result

```
theorem Langlands.Global.uniformTemperednessCriterion_of_halfModulusRootProduct
    (hHM : HalfModulusRootProductStatement.{0}) : UniformTemperednessCriterionStatement
```

The uniform temperedness criterion (Mœglin–Waldspurger 1995, Lemma I.4.1; Delorme 2023,
Proposition 3.6), stated in `Langlands.Global.AdelicUniformTemperednessCriterionStatement`,
holds whenever the half-modulus comparison `HalfModulusRootProductStatement` holds. That
statement is in `Langlands.Global.AdelicHalfModulusRootProductStatement`: on the split component
of a standard parabolic, `|δ_P^{1/2}|²` is the product of the positive roots with their
multiplicities. This module does not prove it. The exponent of the logarithmic height in the
conclusion is `k = 2m`, where `m` is the order of the shift equations.

## Other declarations

- `StandardParabolicFamily.exists_torusPoint_eq_mul`: let `Z₀ → T` be a split component of `G`.
  For `z ∈ A_G` and a positive point `b` of `T₀ → T`, there is a positive point `u` of `T` with
  image `z · a(b)` in `G(𝔸)` and `|β(u)| = |β(b)|` for every relative root `β`. Here `A_G` is the
  positive image of `Z₀` (`imageSubgroup_eq_canonicalSubgroup`), and relative roots vanish on the
  central torus `Z₀` (`root_restrict_eq_zero_of_isCentral`).
- `StandardParabolicFamily.siegel_bound_of_family`: the bound for one standard parabolic family,
  one coordinate frame and one Siegel torus `T₀ → T` with split component `Z₀ → T`. It assumes
  the half-modulus statement, a closed matrix embedding `rho` of size `N > 0`, uniform moderate
  growth of `f` at an open level, and subunitary shift equations of order `m` for the constant
  terms along every standard index. The exponent of the logarithmic height is `2m`.
- `siegel_bound_of_size_zero`: if `rho` is a closed matrix embedding of size `0`, then `G(𝔸)` is
  a point (it embeds into `GL_0(𝔸)`), all roots are trivial on `T(𝔸)`, the Siegel modulus is
  `1`, and for a family with uniform moderate growth the bound holds with every exponent.

## Proof

Let `(T, i, ν, T₀, j)` be a Siegel setup, `t` a threshold and `Ω` compact. The setup provides
`IsMaximalSplitTorus i`, `IsGenericCocharacter i ν` and a split component `Z₀ → T`. If `N = 0`,
use `siegel_bound_of_size_zero`. Otherwise take the standard parabolic family
`𝓕 = ofMaximalSplitTorus` of `(T, i, ν)` and a frame `Fr` (`TorusFrame.nonempty`).

In `siegel_bound_of_family`:

1. `family_growth_bounds` gives the growth hypotheses of `constantTerm_chamber_bound`.
   Smoothness and level come from membership in the smooth subrepresentation and from
   `IsUniformGrowthFamily`. The shift equations along `J ⊇ J'` come from the subunitary shift
   equations of `C_{J'} f x` by `hasTorusShiftEquations_of_le` and `hHM`.
2. Put `θ = |log t| ∑_α step(α)⁻¹`. `constantTerm_chamber_bound` for the top index `𝓕.top`
   (where the constant term is the identity, `constantTerm_top`) gives `C` with
   `‖f x (t' ϖ)‖ ≤ C (2m ‖t'‖ + 3)^{2m} δ_T(t')^{1/2}` for positive `t'` with root coordinates
   at least `-θ`.
3. For `z ∈ A_G` and `b` in the weak chamber `|α(b)| ≥ t`, `exists_torusPoint_eq_mul` gives `u`
   with image `z a(b)`. The root coordinates of `u` are `log |α(b)| / step α ≥ -θ`, and
   `δ_T(u) = siegelModulus b`.
4. With `y = z a(b) ϖ`, `‖u‖ ≤ A log ‖torusPoint u‖ + B` (`exists_crd_le_log_height`),
   `‖torusPoint u‖ ≤ ‖y‖ ‖ϖ⁻¹‖`, and `log ‖y‖ ≤ log N^{∑ mult} + σ(y)`
   (`AdelicSiegelFactors.log_adelicHeight_le`). Since `σ(y) ≥ 1`, these give
   `2m ‖u‖ + 3 ≤ c₁ σ(y)` with `c₁` depending only on the data and `Ω`. Hence
   `‖f x (y)‖ ≤ C c₁^{2m} δ(b)^{1/2} σ(y)^{2m}`.

The proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Source

Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), Lemma I.4.1 (printed
pp.49–51);
P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023), Proposition 3.6
(p.13) and the uniform version stated in the proof of Proposition 4.1 (p.17) (registered as
`moeglin-waldspurger-1995-spectral-decomposition` and
`delorme-2023-spectral-theorem-langlands`). The route is described in the pages of the modules
`AdelicUniformTemperednessExtrapolation`, `AdelicUniformTemperednessDecay` and
`AdelicUniformTemperednessInduction`.
