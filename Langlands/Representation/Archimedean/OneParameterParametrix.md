# A second-order one-parameter parametrix for smooth vectors

`Langlands.Representation.Archimedean.OneParameterParametrix`, namespace
`Langlands.Archimedean.OneParameterParametrix`. A one-variable identity `δ = a'' + b` with
continuous compactly supported kernels, its use along one-parameter subgroups of a group with a
charted-space structure, and its iteration over finitely many one-parameter subgroups. Smooth
vectors, `lieDerivative` and `iteratedLieDerivative` are those of
`Langlands.Representation.Archimedean.SmoothVectors`: `lieDerivative 𝓘(ℝ, E) π X w` is the
manifold derivative at `1` of the orbit `g ↦ π(g) w`, applied to `X` in the model space `E`.

## The one-variable identity

- `cutoff ε t = smoothTransition (2 - 3t/ε)` (Mathlib's `Real.smoothTransition`). It is smooth
  (`contDiff_cutoff`), equal to `1` for `t ≤ ε/3` (`cutoff_eq_one`) and to `0` for `t ≥ 2ε/3`
  (`cutoff_eq_zero`) when `ε > 0`, and its first two derivatives vanish for `t < ε/3` and for
  `t > 2ε/3` (`deriv_cutoff_eq_zero`).
- `secondKernel ε t = max(t, 0) · cutoff ε t` and
  `zerothKernel ε t = -(2 ζ'(t) + t ζ''(t))` with `ζ = cutoff ε`. Both are continuous
  (`continuous_secondKernel`, `continuous_zerothKernel`), vanish outside `(0, ε]` for `ε > 0`
  (`secondKernel_eq_zero`, `zerothKernel_eq_zero`), and so have topological support in `[-ε, ε]`
  (`tsupport_secondKernel_subset`, `tsupport_zerothKernel_subset`). The second kernel is not
  differentiable at `0`; only continuity is used.
- `eq_integral_secondKernel_add`: for a real Banach space `V`, `ε > 0` and `F, F', F'' : ℝ → V` with
  `F' = dF/dt`, `F'' = dF'/dt` everywhere and `F''` continuous,
  `F(0) = ∫ secondKernel ε t • F''(t) dt + ∫ zerothKernel ε t • F(t) dt` (integrals over `ℝ`).

  Proof. Put `Φ(t) = (t ζ(t)) F'(t) - (ζ(t) + t ζ'(t)) F(t)`. Its derivative is
  `t ζ(t) F''(t) - (2 ζ'(t) + t ζ''(t)) F(t)`, which on `(0, ε]` is
  `secondKernel ε t • F''(t) + zerothKernel ε t • F(t)`. Since `ζ(0) = 1` and `ζ(ε) = ζ'(ε) = 0`,
  `Φ(0) = -F(0)` and `Φ(ε) = 0`, so the fundamental theorem of calculus on `[0, ε]`
  (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) gives `F(0) = ∫_{(0, ε]} (…)`; the kernels
  vanish outside `(0, ε]`, so the integral over `(0, ε]` is the integral over `ℝ`.

As distributions, the identity says `δ = a'' + b` with `a = secondKernel ε`, `b = zerothKernel ε`:
`t ↦ max(t, 0)` is a fundamental solution of `d²/dt²`, and multiplying it by the cut-off `ζ`
changes its second derivative by the smooth function `-b` supported in `[ε/3, 2ε/3]`.

## Along one-parameter subgroups

The group `G` carries a topology and a charted-space structure modelled on a real normed space `E`;
`π : G →* (V →L[ℂ] V)` with `V` a complex normed space.

- `iteratedLieDerivative_append`: `dπ(Xs ++ Ys) = dπ(Xs) ∘ dπ(Ys)` on words.
- `curveProd γ t = γ₀(t₀) γ₁(t₁) ⋯ γ_{m-1}(t_{m-1})` for curves `γ : Fin m → ℝ → G`;
  `curveProd_zero`, `curveProd_succ` (`curveProd γ t = γ₀(t₀) · curveProd (tail γ) (tail t)`), and
  `continuous_curveProd` in a topological group.
- `hasDerivAt_orbit_oneParameter`: if `γ : ℝ → G` is smooth (`ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞`) with
  `γ(s + t) = γ(s) γ(t)`, and `w` is a smooth vector, then `s ↦ π(γ s) w` has derivative
  `π(γ t)(lieDerivative 𝓘(ℝ, E) π X w)` at every `t`, where `X = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 1`.
  At `t = 0` this is the chain rule for manifold derivatives (`HasMFDerivAt.comp`) applied to the
  orbit map and `γ`, with `γ(0) = 1`; at general `t`, `π(γ s) w = π(γ t) π(γ(s - t)) w` and `π(γ t)` is
  a continuous linear map. No Lie-group hypothesis is needed.
- `lieDerivative_commute`, `isSmoothVector_of_commute`, `iteratedLieDerivative_commute`: a bounded
  operator `T` with `T π(g) = π(g) T` for all `g` maps smooth vectors to smooth vectors and commutes
  with `lieDerivative` and (for a Lie group) with `iteratedLieDerivative`: the orbit of `T u` is
  `T` composed with the orbit of `u`, and `T` is its own derivative
  (`ContinuousLinearMap.mfderiv_eq`).

## Iteration

- `integral_smul_sum_integral_cons`: in a topological group, for a strongly continuous `π`
  (`g ↦ π(g) v` continuous for each `v`) on a complex Banach space, continuous curves `γᵢ`, a
  continuous `c` on `ℝ` supported in `[-ε, ε]` and continuous kernels `K_j` on `ℝᵐ` supported in the
  closed `ε`-ball (sup norm),
  `∫ c(s) π(γ₀ s)(∑ⱼ ∫ K_j(t') π(curveProd (tail γ) t') v_j dt') ds =
  ∑ⱼ ∫ c(t₀) K_j(tail t) π(curveProd γ t) v_j dt` over `ℝ^{m+1}`. The operator `π(γ₀ s)` passes under
  the inner integral (`ContinuousLinearMap.integral_comp_comm`), the integrands on `ℝ × ℝᵐ` are
  continuous and compactly supported, and the double integral is the integral over `ℝ^{m+1}` by
  `Langlands.Analysis.DixmierMalliavin.integral_fin_succ_cons`; the support of the product kernel is
  `Langlands.Analysis.DixmierMalliavin.tsupport_cons_kernel`.
- `exists_sum_integral_curveProd`: let `G` be a Lie group and a topological group, `ε > 0`, and
  `γ₀, …, γ_{m-1} : ℝ → G` smooth with `γᵢ(s + t) = γᵢ(s) γᵢ(t)`. There are `N`, words
  `word : Fin N → List E` and continuous kernels `K_j` on `ℝᵐ` with topological support in the closed
  `ε`-ball such that for every strongly continuous `π` on a complex Banach space and every smooth
  vector `w`,
  `w = ∑ⱼ ∫ K_j(t) π(curveProd γ t)(iteratedLieDerivative 𝓘(ℝ, E) π (word j) w) dt`.
  The words and kernels do not depend on `π` or `w`.

  Proof by induction on `m`. For `m = 0` take one empty word and `K = 1` (the volume of `ℝ⁰` is `1`).
  For `m + 1`, let `X₀ = mfderiv γ₀ 0 1`, `w₁ = dπ(X₀) w`, `w₂ = dπ(X₀) w₁` (smooth by
  `isSmoothVector_lieDerivative`). By `hasDerivAt_orbit_oneParameter` the identity
  `eq_integral_secondKernel_add` applies to `F(s) = π(γ₀ s) w`, `F' = π(γ₀ s) w₁`,
  `F'' = π(γ₀ s) w₂`; since `γ₀(0) = 1` it reads `w = ∫ a(s) π(γ₀ s) w₂ ds + ∫ b(s) π(γ₀ s) w ds`.
  Expanding `w₂` and `w` by the induction hypothesis for `γ₁, …, γ_m` and combining with
  `integral_smul_sum_integral_cons` gives the identity for `γ₀, …, γ_m` with the `2N` words
  `word j ++ [X₀, X₀]` and `word j` (`iteratedLieDerivative_append`) and kernels
  `a(t₀) K_j(tail t)` and `b(t₀) K_j(tail t)`.

## Literature

The iteration over finitely many one-parameter subgroups follows J. Dixmier and P. Malliavin,
*Factorisations de fonctions et de vecteurs indéfiniment différentiables*, Bull. Sci. Math. (2) 102
(1978), §3, proof of Theorem 3.1, steps (2)–(3), pp. 6–7 of the English translation *Factorizations of
infinitely differentiable functions and smooth vectors* (paginated 1–24): a one-variable identity
along `t ↦ exp(t x₁)`, then repeated along `x₂, …, x_m`, with the product measure carried to `G` by
`(t₁, …, t_m) ↦ (exp t₁x₁) ⋯ (exp t_m x_m)`. Their one-variable identity is Lemma 2.5(3) with
Remark 2.6 (pp. 5–6 there), `∑ₙ (-1)ⁿ αₙ δ^{(2n)} * g → δ + h` with `g, h` smooth and of support in
`[-ε, ε]`, an identity of infinite order needed for their factorization with smooth functions. Here
the elementary second-order identity `δ = a'' + b` takes its place: it involves only one derivative
order, and its price is that the kernel `a` is continuous but not smooth. The identity itself is a
standard parametrix for `d²/dt²` (a cut-off fundamental solution); the formula with
`Φ = (tζ) F' - (tζ)' F` is the proof implemented here.
