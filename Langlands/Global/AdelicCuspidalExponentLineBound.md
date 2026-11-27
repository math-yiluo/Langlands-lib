# Cuspidal components with a negative exponent along a maximal parabolic of `M_R`

Module `Langlands.Global.AdelicCuspidalExponentLineBound`. It states and proves
`Langlands.Global.StandardParabolicFamily.CuspidalExponentLineBoundStatement` (theorem
`cuspidalExponentLineBound`). Let `R = Q ∪ {β}` with `β ∉ Q`. A function on
`U_Q(𝔸) M_Q(F) \ G(𝔸)` that is cuspidal along `Q` and has one unnormalized exponent `λ` along
`Q` with `⟨Re λ, β^∨⟩ < 0` is bounded on Siegel regions of the Levi `M_R`.

This is the bound for one component that Bernstein–Lapid use in their application of
Mœglin–Waldspurger I.4.1 (§6.4). For an unnormalized exponent `λ` the corresponding term of the
majorant of I.4.1 is `m_{P_0}(g)^{Re λ} (1 + ‖log m_P(g)‖)^{deg}`. Mœglin–Waldspurger write this
power as `Re π + ρ_P`, with `π` the normalized exponent and `P` the parabolic subgroup, of the
group to which I.4.1 is applied, that carries the exponent. By the decomposition (6.10) of
Bernstein–Lapid, `𝒜_{P,π} = 𝒜^{un}_{P,π+ρ_P}`, so `Re π + ρ_P` is the real part `Re λ` of the
unnormalized exponent. Here the exponent is attached to the maximal parabolic of `M_R` with Levi
`M_Q`, and `Re λ` pairs negatively with `β^∨`.

## Analytic lemmas (namespace `Langlands.Analysis`)

- `exists_exp_mul_one_add_abs_pow_le`: for `δ > 0` and `h₀`, `e^{-δ t} (1 + |t|)^n` is bounded on
  `[h₀, ∞)`. With `s = t − h₀ ≥ 0` and `K = 1 + |h₀|` one has `1 + |t| ≤ K (1 + s)`, and
  `(1 + s)^n ≤ n! e^δ δ^{-n} e^{δ s}` by `Real.pow_div_factorial_le_exp`.
- `exists_norm_eval_le`: a complex polynomial `p` satisfies `|p(t)| ≤ A (1 + |t|)^{deg p}` on `ℝ`.
- `exists_exp_mul_norm_eval_le_sum`: for `δ > 0`, `n` and `h₀` there is `M` such that every
  complex polynomial `q` of degree at most `n` satisfies
  `e^{-δ t} |q(t)| ≤ M ∑_{i=0}^{n} |q(i)|` for `t ≥ h₀`. It writes `q` as its Lagrange
  interpolation at the nodes `0, …, n` (Mathlib's `Lagrange.eq_interpolate`) and applies the two
  previous lemmas to the Lagrange basis polynomials.
- `exists_polynomial_natDegree_le_eval_smul`: on a line `t ↦ t • H`, an element of
  `polynomialFunctions V n` is a complex polynomial of degree at most `n` in `t`. The proof is by
  induction on the span.

## Root-theoretic lemmas

- `exists_corootProjection`: for `Q ⊆ R` and a simple root `β` of `R`, the projection `w` of
  `β^∨` to `𝔞_Q = rootAnnihilator 𝓕.T Q` along the span of the coroots of `Q`. This uses the
  decomposition `𝔞_0 = 𝔞_Q ⊕ 𝔞_0^Q` of the published `standardLeviRealDecomposition`. The roots of
  `Q` vanish on `w`. Every element of `corootAnnihilator R` vanishes on `w`. Every element of
  `corootAnnihilator Q` takes the same value on `w` as on `β^∨`. Finally `β^∨ − w` lies in the
  span of the coroots of `Q`.
- `realExponent_mem_corootAnnihilator` in `AdelicLeadingCuspidalInjectivityReduction`: `Re λ` (`realExponent Q λ`) is annihilated by the
  coroots of `Q`. It is the restriction of a real character of `M_Q`, and the published
  `standardLeviCharacterAnnihilator` identifies these restrictions with `corootAnnihilator Q`.
- `exists_weightForm`: for a simple root `β` of `R` there is `ϖ ∈ 𝔞_0^*` with these properties.
  `ϖ = ∑_{γ ∈ R} W_{βγ} γ`, where `W` is the inverse of the Cartan block of `R` in the published
  root system `ArthurRelative.rootPairing`, so `ϖ` is Arthur's weight
  `ArthurRelative.weight … R β`. Its values are `ϖ(β^∨) = 1` and `ϖ(α^∨) = 0` for the other simple
  roots `α` of `R` (published `weight_coroot`). There is `c ≥ 0` with `ϖ(H) ≥ −c B` whenever every
  root of `R` is at least `−B` on `H`, because the entries of `W` are nonnegative (published
  `cartanBlock_inv_nonneg'`). Finally `β` lies in the span of `ϖ` and the other simple roots of
  `R`, because `W_{ββ} ≥ 1/2` (published `half_le_cartanBlock_inv_self`).
- `cocharacterFunctional_add`, `exists_splitComponent_of_log` and
  `eq_map_torus_of_map_parabolic_eq`. A real cocharacter `v` annihilated by the roots of `Q` is
  the logarithm of a positive torus point `τ` (published `exists_characterLog_eq`). The image of
  `τ` in `G(𝔸)` is the image of a point `s ∈ 𝔄_Q` (published `positiveTorusSplitComponent`). Such
  an `s` equals the image of `τ` in `P_Q(𝔸)`, because `P_Q(𝔸) → G(𝔸)` is injective.

## The statement

`CuspidalExponentLineBoundStatement 𝓕 hG rho` assumes `N > 0`. Let `Q, R` be standard indices and
`β` a relative root with `β ∉ Q` and `R = Q ∪ {β}`. Let `Φ` be a set of real linear forms on `𝔞_0`
contained in `corootAnnihilator R`, such that `Φ` and the simple roots of `R` span `𝔞_0^*`. Fix
a real number `b > 0` (in Lean a unit of `ℝ≥0`), a real number `B ≥ 0`, compact sets
`Ω ⊆ P_0(𝔸)` and `K`, a compact set `Y_f` of finite adelic points and an open finite level `L`.
Let `c : G(𝔸) → ℂ` satisfy:
- it is continuous and smooth on the archimedean slices;
- it is left invariant under `P_0(F)` and `U_Q(𝔸)`, and right invariant under `L`;
- its constant terms along `Q \ {γ}` vanish for every `γ ∈ Q`;
- its derivative words satisfy `|D c(x)| ≤ C_D ht(x)^{R_g}`;
- it has unnormalized exponent `λ` along `Q` (`HasUnnormalizedExponent Q λ c`), with
  `⟨Re λ, β^∨⟩ < 0`.

Then there is `C` with `|c(p a k)| ≤ C`. Here `p ∈ Ω`, `k ∈ K`, and the finite part of `p a k` lies
in `Y_f`. The point `a` is a positive torus point with logarithm `H`. The normalized adelic norms
of the simple roots of `R` at `a` are bounded below by `b`: `|γ(a)|_𝔸 ≥ b` for `γ ∈ R`
(`normCharacter`). The forms of `Φ` are bounded at `H`: `|φ(H)| ≤ B` for `φ ∈ Φ`.

## The proof (`cuspidalExponentLineBound`)

Let `δ = −⟨Re λ, β^∨⟩ > 0`. Let `w` and `ϖ` be as above. Then `ϖ(w) = 1`, since `ϖ` vanishes on the
coroots of `Q` and `β^∨ − w` lies in their span. Also `⟨Re λ, w⟩ = −δ`, since `Re λ` is
annihilated by the coroots of `Q`. For `t ∈ ℝ` let `x_t ∈ 𝔄_Q` be the point with torus logarithm
`t w`. Its logarithm in `P_Q` is `t H₀`. Then `|x_t^λ| = e^{−δ t}` (published
`norm_parameterPower_map_torus`) and `|x_t^{−λ}| = e^{δ t}`.

Fix `p, a, k` in the region, let `H` be the logarithm of `a`, and put `h = ϖ(H)`. Since `b > 0`,
`log b` is defined, and `|γ(a)|_𝔸 ≥ b` gives `γ(H) ≥ log b ≥ −max(0, −log b)` for the simple
roots `γ` of `R`; hence `h ≥ −c max(0, −log b)`. For `t ∈ ℝ` let `a_t` be the positive torus point
with logarithm `H + (t − h) w`, namely `a` multiplied by the torus points of logarithms `−h w`
and `t w`. Then `a_h = a`, and `a_0` has logarithm `H − h w`. Put `g₀ = p a_0 k`. Every point of
`𝔄_Q` passes `p ∈ P_Q(𝔸)` on the left, by `U_Q(𝔸)`-invariance
(`IsRadicalInvariant.splitComponent_mul_comm`). Hence `c(x_t g₀) = c(p a_t k)` for all `t`. By
the exponent hypothesis at `g₀`, `c(x_t g₀) x_t^{−λ} = q(t)` for a complex polynomial `q` of
degree at most `n` (`exists_polynomial_natDegree_le_eval_smul`). Therefore
`c(p a k) = c(p a_h k) = x_h^λ q(h)`, and

`|c(p a k)| = e^{−δ h} |q(h)| ≤ M ∑_{i=0}^{n} |q(i)| = M ∑_{i=0}^{n} |c(p a_i k)| e^{δ i}`

by `exists_exp_mul_norm_eval_le_sum`.

Each point `a_i` lies in a Siegel region of `M_Q`, to which
`relativeCuspidalRegionDecay` (module `Langlands.Global.AdelicShiftedMaximalDecay`) applies, with
`J = Q`, `Φ_Q = Φ ∪ {ϖ}` and bound `max(B, n)`:
- the norms `|γ(a_i)|_𝔸` for `γ ∈ Q` equal those at `a`, hence are at least `b`, because the
  roots of `Q` vanish on `w`;
- the forms of `Φ` take the same values, because they vanish on `w`;
- `ϖ` takes the value `i ∈ [0, n]`;
- `Φ_Q` and the roots of `Q` span `𝔞_0^*`, because `β` lies in the span of `ϖ` and the roots of
  `Q`;
- the finite part of `p a_i k` is that of `p a k`.
With height exponent `0` this gives one constant `C_B` with `|c(p a_i k)| ≤ C_B` for all nodes
and all points of the region, and `|c(p a k)| ≤ M (n + 1) C_B e^{δ n}`.

## Sources and provenance

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.4.1 (p. 49), the bound of an
  automorphic form on a Siegel set by
  `∑ m_{P_0}(g)^{Re π + ρ_P} (1 + ‖log m_P(g)‖)^{deg}` over its cuspidal data.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series* (2024),
  registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`: the decomposition
  (6.10) (p. 203), relating normalized and unnormalized exponents, and §6.4 (p. 204), where
  I.4.1 is applied to forms whose cuspidal exponents attached to maximal parabolics pair
  negatively with the coroot.

The statement is derived. It bounds the contribution of one cuspidal exponent component in
MW I.4.1, for an exponent attached to a maximal parabolic `Q` of `M_R` and negative on `β^∨`. On
the Siegel region of `M_R` the logarithm of the `𝔄_Q`-component is `ϖ_β(H) w` up to a bounded
term, and `ϖ_β(H)` is bounded below (Arthur's positivity of weights on the positive chamber).
The polynomial interpolation is internal to this module. It replaces the estimate of the
exponent polynomial in MW's proof.
