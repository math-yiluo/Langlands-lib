# Harish-Chandra equations for Eisenstein series (Bernstein–Lapid (8.2a))

Module `Langlands.Global.AdelicEisensteinHarishChandraEquations`.

Source: J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), §8.4, journal p.223. There BL
fix pairs `(h_i(λ), c_i(λ))`, `i ∈ I`. Each `h_i(λ)` is a holomorphic family of smooth,
compactly supported, bi-`K`-finite functions on `G(𝔸)`, and each `c_i` is holomorphic. The
pairs satisfy:

1. `δ(h_i(λ)) E(φ, λ) = c_i(λ) E(φ, λ)` for all `i` when `⟨Re λ, α^∨⟩ ≫ 0`;
2. for every `λ₀` some `c_i(λ₀) ≠ 0`.

These pairs give the equations (8.2a) of the system `Ξ_fnl(λ)`. BL obtain them from
Lemma 8.3, applied to `E(φ, λ)` through Lemma 8.2 and the constant-term formula (6.18). This
module takes a different route. It applies the uniform Harish-Chandra equations to the twists
`φ_λ` on `U(𝔸) M(F) \ G(𝔸)`, which is `InducedHarishChandraEquationsStatement` in
`Langlands.Global.AdelicInducedHarishChandraStatement`. Then it sums over `P(F) \ G(F)`.
Provenance: derived.

The module contains a statement of BL's (8.2a) data, a proof that it follows from
`InducedHarishChandraEquationsStatement`, and supporting definitions and lemmas. It does not prove
`InducedHarishChandraEquationsStatement` itself.

## Supporting definitions and lemmas

- `isHolomorphicOn_opens_of_differentiable`: if `f : ℂⁿ → ℂ` is complex differentiable,
  then for every open `W ⊆ ℂⁿ` the restriction `s : W ↦ f s` satisfies the Library's
  `IsHolomorphicOn 𝓘(ℂ, ℂⁿ) _ Set.univ`. This is the holomorphy condition of
  `LocalFinitenessData.IsAdmissible`. Proof: a continuous linear form on `ℂ` composed with
  `f` is differentiable, hence manifold-differentiable. The inclusion of the open subset `W`
  is smooth (`contMDiff_subtype_val`), and the composite is differentiable.
- `AdelicGroupPoints.parabolicCosetRep p q` is the representative in `G(F) ⊆ G(𝔸)` of
  `q ∈ P(F) \ G(F)` that the Library's Eisenstein series uses (`Quotient.out`).
- `AdelicGroupPoints.IsIwasawaCompact.continuous_parameterTwist`: if `φ` is continuous, so
  is `φ_λ = φ · exp⟨λ, H_P⟩`. The proof uses the continuity of the Iwasawa height
  (`IsIwasawaCompact.continuous_height`) and of the pairing with `λ`.
- `AdelicGroupPoints.IsIwasawaCompact.rightConvolution_eisensteinSeries`. Let `φ` and `h` be
  continuous, `h` compactly supported, and `x ∈ G(𝔸)`. Suppose that for `g` in the support
  of `h` the Eisenstein terms satisfy `‖φ_λ(γ_q x g)‖ ≤ B q` with `B` summable over
  `q ∈ P(F) \ G(F)`. Then the values `(δ(h) φ_λ)(γ_q x)` are summable over `q`, and
  `δ(h) E(φ, λ)(x) = ∑_q (δ(h) φ_λ)(γ_q x)`.
  - The function `g ↦ h(g) φ_λ(γ_q x g)` is continuous and compactly supported, hence
    integrable for the Haar measure.
  - The norm of this function is at most `‖h(g)‖ B q`, so its integral is at most
    `(∫ ‖h‖) B q`. These bounds are summable in `q`.
  - `integral_tsum_of_summable_integral_norm` exchanges the integral with the sum over `q`.
  - The Library's `eisensteinSeries` is the sum of these terms
    (`∑' q, φ_λ(γ_q · x g)`). Multiplication by `h(g)` commutes with this sum
    (`tsum_mul_left`), and `γ_q (x g) = (γ_q x) g`.

## The statement `EisensteinHarishChandraEquationsStatement`

The setting is that of `EisensteinAbsoluteConvergenceStatement` with
`LocallyOfFiniteType G.X.hom`. Let `φ` be an automorphic form on `U(𝔸) M(F) \ G(𝔸)`. Then
there is a real `R` with the following property. For all `n` and linear coordinates
`e : ℂⁿ ≃ₗ[ℂ] X^*(P) ⊗ ℂ`, there are:

- an index type `Idx : Type u`;
- for every `i ∈ Idx`, a number `m i` and functions `h i k` (`k < m i`) that are smooth,
  compactly supported test functions (`IsAdelicTestFunction`) and finite under left and
  right translation by `K_∞`;
- complex differentiable functions `b i k`, `c i : ℂⁿ → ℂ`.

These satisfy:

- for every `s ∈ ℂⁿ` there is `i` with `c i s ≠ 0`;
- at every `s` such that `e s` is `R`-regular (`r.IsRegularParameter hA hT R (e s)`, the
  region of absolute convergence), and for every `i` and `x ∈ G(𝔸)`,
  `∑_k b i k s · δ(h i k)(E(φ, e s))(x) = c i s · E(φ, e s)(x)`, where `E(φ, λ)` is
  `hK.eisensteinSeries φ λ`.

This is BL's (8.2a) data with `h_i(λ) = ∑_k b_{ik}(λ) h_{ik}` and BL's regularity
`⟨Re λ, α^∨⟩ ≫ 0` in the form `R`-regular. The equations are tested pointwise at every
`x ∈ G(𝔸)`. This is the form of the convolution conjunct of `LocalFinitenessData.solutions`,
and the form that `AdelicEisensteinScalarEquations` turns into continuous scalar equations.
Since `R`-regularity for a larger `R` implies it for a smaller one, the equations also hold
at `R₀`-regular parameters for every `R₀ ≥ R`.

## The reduction `eisensteinHarishChandraEquations_of_induced`

`InducedHarishChandraEquationsStatement.{u} → EisensteinHarishChandraEquationsStatement.{u}`.

1. `R` is the constant of `eisensteinAbsoluteConvergence`, the Library's proof of
   `EisensteinAbsoluteConvergenceStatement`. It does not depend on `n` or `e`.
2. Put `Idx = ULift (ℂⁿ)`. For `i = s₀`, take the data `h`, `b`, `c` that
   `InducedHarishChandraEquationsStatement` gives at `s₀`. Then `c i s₀ ≠ 0`, which gives
   the nonvanishing condition at every `s`.
3. Fix an `R`-regular `s`, `i` and `x`. For each `k`, the set `C = x · supp(h i k)` is
   compact. `eisensteinAbsoluteConvergence`, applied to `C` and the compact parameter set
   `{s}`, gives a summable majorant of the terms `φ_{e s}(γ_q g)` for `g ∈ C`.
   `rightConvolution_eisensteinSeries` then gives `δ(h i k) E(x) = ∑_q δ(h i k)φ_{e s}(γ_q x)`
   with a summable right-hand side.
4. Multiply by `b i k s` and sum over `k`. The finite sum and the sum over `q` commute by
   summability. The equation of `InducedHarishChandraEquationsStatement` at the point `γ_q x`
   turns the `q`-th term into `c i s · φ_{e s}(γ_q x)`. Summing over `q` gives
   `c i s · E(φ, e s)(x)`.

Only the regularity of the single point `s` is used. The equations for the twists hold at
every parameter.
