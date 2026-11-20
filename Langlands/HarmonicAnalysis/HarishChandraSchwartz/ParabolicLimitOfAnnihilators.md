# Parabolic limits from annihilators at strict points

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicLimitOfAnnihilators`.

This is a helper module for the proof of Waldspurger's Lemma III.5.1
(`RationalOrbitWeakConstantTermLimitStatement`). It is internal, derived content. It gives an
abstract criterion for `TendstoZeroAlongParabolic` (Waldspurger III.5, printed p. 269:
`lim_{a →_P ∞} f(a) = 0`). The estimates follow the proof of Waldspurger's Lemma VI.2.3, as
already formalised in `PositivePartDecay`. They are used only at finitely many strict points,
which are chosen after the cone parameter `η` is fixed.

## Declarations

- `HasHalvingDecay φ z N` (definition, a `Prop`): whenever `‖φ(b zᵉ)‖ ≤ C` for all `e < N`
  (with `C ≥ 0`), we get `‖φ(b zⁿ)‖ ≤ C 2^N 2^{-n}` for every `n`.
- `one_le_two_pow_mul_half_pow`: `1 ≤ 2^N 2^{-n}` for `n ≤ N`.
- `exists_hasHalvingDecay_pow` (**one direction**): let `P` be monic with all roots of modulus
  at most `θ < 1`, and suppose `P(ρ(y)) φ = 0`, where `ρ` is right translation. Then there is
  `q₀` such that `φ` has halving decay along `y^q` with `N = deg P` for every `q ≥ q₀`.
  - Proof: `exists_pow_coeff_small` makes the coefficients of `rootPowerPolynomial P q₀` small.
    The same bound holds for every larger `q`, because `θ'^q ≤ θ'^{q₀}` with `θ' = max θ 0`.
  - `aeval_rootPowerPolynomial_eq_zero` shows that this polynomial kills `φ` under `ρ(y^q)`.
  - `norm_le_of_aeval_eq_zero` then applies with `K = C 2^N`. Its initial bound holds because
    `2^N 2^{-e} ≥ 1` for `e < N`.
- `norm_mul_prod_le_of_hasHalvingDecay` (**several directions**, `G` commutative): suppose `φ`
  has halving decay along `z i` with `N i` for each `i ∈ s`, and
  `‖φ(a ∏_{i∈s} z_i^{e_i})‖ ≤ C` whenever `e_i < N_i` for all `i ∈ s`. Then
  `‖φ(a ∏ z_i^{n_i})‖ ≤ C ∏_{i∈s} 2^{N_i} · 2^{-∑ n_i}` for all `n`.
  - Proof by induction on `s`. To add a direction `j`, apply the induction hypothesis to the
    base points `a z_jᵉ` with `e < N_j`. This needs the hypothesis at `Function.update e' j e`.
  - Then apply halving decay along `z_j` at `b = a ∏_{i∈s} z_i^{n_i}`.
- `exists_shellDecomposition` (pure real arithmetic). The data are a nonempty finite set `S` of
  cardinality `k`, weights `γ_i ≥ 0`, `Λ > 0` and `η > 0` with `2k ∑ γ ≤ η Λ`, `M ≥ 0` and
  `T₀ ∈ ℕ`.
  - Conclusion: there is `R > 0` such that every `v` with `v_i > R` and `v_i > η v_j` can be
    written `v_i = γ_i ∑_j n_j + Λ n_i + r_i`.
  - Here `n ∈ ℕ^S`, `∑ n ≥ T₀` and `M ≤ r_i ≤ M + k γ_i + Λ`.
  - Proof: put `w = v − M` and `U = ∑ w / (Λ + ∑ γ)`. Solve `u_i = (w_i − U γ_i)/Λ` exactly, so
    that `∑ u = U`, and set `n_i = ⌊u_i⌋₊`.
  - The cone condition and `2k ∑γ ≤ ηΛ` give `γ_i U ≤ w_i`, so `u_i ≥ 0`.
  - The flooring errors give the bounds on `r_i`. Finally `U > T₀ + k` once `R` is large.
- `aeval_rightFunctions_comp` and `aeval_rightFunctions_comp_eq_zero` (**transport**): suppose
  `f (y x) = f(y) j(x)`, where `j` is a homomorphism. Then `P(ρ(x)) (p ∘ f) = (P(ρ(j x)) p) ∘ f`.
  - Proof: expand both sides with `aeval_eq_sum_range` and use `f(y xᵏ) = f(y) j(x)ᵏ`.
  - Consequence: an annihilator of `p` under `ρ(j x)` also annihilates `p ∘ f` under `ρ(x)`.
- `continuous_of_mul_right_invariant`: on a topological group, let `f` be invariant under right
  translation by an open set `H ∋ 1`. Then `f` is continuous, since it is constant on the open
  neighbourhood `m H` of each `m`.
- `exists_bound_of_latticeSection` (**bounds on shells**). The data are a lattice section
  `sec : L → A` and a compact set `N` such that every `x` is `n · sec c` with `n ∈ N`.
  - Assume the coordinates `coord α (n · sec c)` equal `pair α c` for `α ∈ S`.
  - Assume `Φ` is continuous and invariant under `sec` of the common kernel of the `pair α`.
  - Conclusion: `Φ` is bounded above on each shell `{R₀ < coord α ≤ B, α ∈ S}`.
  - Proof: the possible coordinate vectors form a finite integer box. For each vector in the box
    that has a lattice preimage, choose one preimage `rep v`. Then `Φ` is bounded on the compact
    finite union of the sets `sec(rep v) · N`.
  - Write `x = (n · sec(rep v)) · sec(c − rep v)`. Here `c − rep v` lies in the common kernel,
    so `Φ(x) = Φ(sec(rep v) · n)`.
- `tendstoZeroAlongParabolic_of_strictAnnihilators` (**main result**). The data are an additive
  `HM : A → E` on a commutative group, a finite set `S` of linear forms, a subgroup `T`, and
  `φ : A → ℂ`. The hypotheses are:
  1. Every `y ∈ T` with `α(HM y) > 0` for all `α ∈ S` has a monic annihilator `P(ρ(y)) φ = 0`
     whose roots have modulus at most some `θ < 1`.
  2. There is `g₀ ∈ T` with `α(HM g₀) > 0` for all `α ∈ S`.
  3. There are `d > 0` and, for each `β ∈ S`, an element `h β ∈ T` with `β(HM(h β)) = d` and
     `α(HM(h β)) = 0` for every other `α ∈ S`.
  4. There is `R₀` such that, for every `B`, `φ` is bounded on the deep shell
     `{a : R₀ < α(HM a) ≤ B for all α ∈ S}`.

  Conclusion: `TendstoZeroAlongParabolic HM S φ`.

## Proof of the main result

- **`S = ∅`.** Hypothesis 4 makes `φ` bounded on `A`. Halving decay along a power `z` of `g₀`
  gives `‖φ(a)‖ = ‖φ((a z^{-n}) zⁿ)‖ ≤ C 2^N 2^{-n}` for all `n`, so `φ = 0`.
- **`S ≠ ∅`.** Fix `ε` and `η`, and let `k = |S|`. Choose `m` with
  `2k ∑_α α(HM g₀) ≤ η (m+1) d`. The strict directions are `y_β = g₀ (h β)^{m+1} ∈ T`.
  - Their coordinates are `α(HM y_β) = α(HM g₀) + [α = β](m+1)d`.
  - Hypothesis 1 and `exists_hasHalvingDecay_pow` give halving decay along `z_β = y_β^q`, with
    one common `q` (one plus the maximum of the `q₀`).
- For `a` in the region `{R < α(HM a), η β(HM a) < α(HM a)}`, apply `exists_shellDecomposition`
  to `v_α = α(HM a)`, with `γ_α = q α(HM g₀)` and `Λ = q(m+1)d`.
  - The margin is `M = max R₀ 0 + 1`. The step count `T₀` is chosen so that
    `max C 0 · ∏ 2^{N_β} · 2^{-T₀} < ε`, where `C` is the deep-shell bound from hypothesis 4.
  - The shell ceiling is `B = M + kΓ + Λ + (∑ N)(Γ + Λ)`, where `Γ = ∑ γ`.
- Write `a = a' ∏ z_β^{n_β}`. Then every point `a' ∏ z_β^{e_β}` with `e < N` has coordinates in
  `[M, B]`, so it lies in the deep shell.
- `norm_mul_prod_le_of_hasHalvingDecay` gives
  `‖φ(a)‖ ≤ max C 0 · ∏ 2^{N_β} · 2^{-∑ n} ≤ max C 0 · ∏ 2^{N_β} · 2^{-T₀} < ε`.
