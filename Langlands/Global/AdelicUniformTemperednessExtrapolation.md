# Extrapolation of constant terms along dominant split-component directions

Module `Langlands.Global.AdelicUniformTemperednessExtrapolation`, namespace
`Langlands.Global.StandardParabolicFamily`.

## Definitions

- `torusModulus 𝓕 x = ∏ᶠ_{β ∈ Φ⁺} |β(x)|^{m_β}` on `T(𝔸)`, where `m_β` is the dimension of the
  `β`-weight space of `T` on the Lie algebra of `G` (`Module.finrank F (weightSpace 𝓕.i β)`).
  On positive points this is the modulus `δ_{P₀}` of the minimal standard parabolic, as in
  `siegelModulus`.
- `torusPoint x`: the image of `x ∈ T(𝔸)` in `G(𝔸)`.
- `HasTorusShiftEquations 𝓕 J m φ`, for an arbitrary set `J` of characters of `T`: for every
  positive point `t` of `T` at which every character in `J` takes the value `1`
  (`Lie.characterValue β t = 1`) and every simple root has idele norm at least `1`, there are
  `w_0, …, w_{m-1}` with `‖w_k‖ ≤ δ_T(t)^{1/2}` such that left translation by `torusPoint t`
  satisfies `∏_k (L_t - w_k) φ = 0` (`IsTranslationPolynomialSolution`). Every character in
  `J` is tested, whether or not it is a simple root. The case used for the criterion is `J` the
  set of simple roots of a standard index (`J'.1` for `J' : StandardIndex`), where the
  condition says that the simple roots in `J` are trivial at `t`.

## Results

- `exists_torusModulus_eq`: `δ_T = ∏_{α ∈ Δ} |α|^{e_α}` with all `e_α ≥ 1`. This uses
  `AdelicSiegelFactors.exists_simpleRoot_exponents`. Consequences: `torusModulus_pos`,
  `torusModulus_mul`, `torusModulus_pow`, `log_torusModulus` (a linear form in the root
  coordinates), `one_le_torusModulus` (on points with nonnegative root coordinates) and
  `exists_torusModulus_bounds`: `e^{-Λ‖x‖} ≤ δ_T(x) ≤ e^{Λ‖x‖}`, where `‖x‖` is the norm of
  `Fr.crd x`.
- `hasTorusShiftEquations_of_le`: given `HalfModulusRootProductStatement`, subunitary shift
  equations along `𝔄_{J'}` (`HasSubunitaryShiftEquations`, module
  `Langlands.Global.AdelicEisensteinUnitaryExponentStatement`) give torus shift equations along
  every set `J ⊇ J'.1` of characters. A positive point `t` of `T` at which the characters in `J`
  are trivial is the image of a positive point `s` of the split component `A_{J'}`
  (`exists_splitPoint`); the simple roots take the same idele norms at `s` and at `t`, so `s` is
  dominant when every simple root has idele norm at least `1` at `t`. The half-modulus statement
  then gives `‖δ_{P_{J'}}(s)^{1/2}‖² = δ_T(t)`.
- `HasTorusShiftEquations.sub`: if `φ` and `ψ` satisfy equations of orders `m` and `m'`, then
  `φ - ψ` satisfies equations of order `m + m'`, with the concatenated roots.
- `norm_le_of_hasTorusShiftEquations` (**extrapolation**): let `J ⊆ Δ` be a set of simple
  roots and let `φ` satisfy shift equations of order `m` along `J`. Let `x₁` and `w` be positive
  points of `T`, the root coordinates of `x₁` being `0` on `J` and `≥ 0` elsewhere, and let
  `B ≥ 0`. If `‖φ(u ω)‖ ≤ B` for every positive `u` whose coordinates are within `1` of those of
  `w`, then `‖φ(x₁ w ω)‖ ≤ 3^m (m ‖x₁‖ + 3)^m δ_T(x₁)^{1/2} B`.
- `norm_le_of_hasTorusShiftEquations_chamber` (**bound at a chamber point**): let `Λ ≥ 0` satisfy
  the lower bound `δ_T(y) ≥ e^{-Λ‖y‖}` of `exists_torusModulus_bounds` for all `y`. Let `J ⊆ Δ`
  be a set of simple roots, let `φ` satisfy shift equations of order `m` along `J`, and let `x`
  be a positive point of `T`. Let `ρ, ρ' ≥ 0`, the root coordinates of `x` being at most `ρ` in
  absolute value on `J` and at least `-ρ'` everywhere. Let `B ≥ 0` and suppose `‖φ(u ω)‖ ≤ B`
  at every positive `u` whose `J`-coordinates are within `1` of those of `x`, whose other root
  coordinates lie in `[-ρ' - 1, 1]` and whose central coordinates have norm at most `1`. Then
  `‖φ(x ω)‖ ≤ 3^m (m‖x‖ + 3)^m δ_T(x)^{1/2} e^{Λ(ρ + ρ' + 1)} B`.
  The hypothesis `J ⊆ Δ` is needed in both results: the vanishing of the root coordinates of a
  point on `J` is what makes every character of `J` trivial there.

## Proofs

For the extrapolation, put `N = ⌈m ‖x₁‖⌉ + 1` and take the `N`-th root `y` of `x₁` in `A_T`
(`exists_pow_eq`). It satisfies the hypotheses of the shift equations, so `φ` is annihilated
by `∏_k (L_y - w_k)` for some `w_k` with `|w_k| ≤ δ_T(y)^{1/2}`. Write `φ(y^q w ω)` as a sequence in `q`.
The first `m` terms lie in the region where `‖φ‖ ≤ B`, since `j ‖crd y‖ ≤ m ‖x₁‖ / N ≤ 1` for
`j < m`, and `δ_T(y)^{j/2} ≥ 1` because the root coordinates of `y` are nonnegative.
`norm_le_of_translationSolution` (module `Langlands.Analysis.ShiftRecurrenceBound`) with
`κ = δ_T(y)^{1/2}` and `M = B ≥ 0` at `q = N` gives the
bound, because `κ^N = δ_T(x₁)^{1/2}` and `N + 1 ≤ m ‖x₁‖ + 3`.

For the chamber version, split `x = x₁ x₀ x_c` (`exists_split`). Apply the extrapolation to `x₁`
with `w = x₀ x_c`. The points near `w` lie in the hypothesis region, because
`‖crd x₀‖ ≤ ρ'` and the `J`-coordinates of `x_c` are those of `x`. Then
`δ_T(x₁) ≤ δ_T(x) e^{Λ(ρ + ρ')}` by the lower bound for `δ_T(x₀ x_c)` and
`‖crd(x₀ x_c)‖ ≤ ρ + ρ'`,
and `‖crd x₁‖ ≤ ‖crd x‖`.

## Source

Mœglin–Waldspurger 1995, Lemma I.4.1, printed pp.49–51, and the Lemma of I.4.2, printed p.51
(registered as `moeglin-waldspurger-1995-spectral-decomposition`); Delorme 2023, Proposition 3.6
(registered as `delorme-2023-spectral-theorem-langlands`). The finite exponential-polynomial
expansion of constant terms along `A_P` used there is replaced by shift equations along single
translations, a derived device.
