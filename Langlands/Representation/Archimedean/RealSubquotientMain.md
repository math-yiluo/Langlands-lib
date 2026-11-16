# Harish-Chandra's subquotient theorem for `GL_n(ℝ)`: killing `T₀` and the graph argument

Module: `Langlands.Representation.Archimedean.RealSubquotientMain` (namespace
`Langlands.Archimedean.RealSubquotient`).

This is the last helper module for the proof of `RealPrincipalSeriesSubquotientStatement`; see
`RealPrincipalSeriesSubquotientProof.md`. It imports the Library statement module
`RealJacquetSubquotientReduction` for `IsRealSubquotientMap`. Throughout, `τ` is continuous with
derivative `D` (`IsTypeDerivative τ D`).

- `act_eq_self_pow`: if `x · T = T` then `x^m · T = T`. `act_add_right`, `act_smul_right`: `act`
  is linear in the intertwiner.
- `chat_eval_eq_zero_of_kill`: suppose `x` kills every `K`-intertwiner from `τ` into
  `PS a e`, for every sign vector `e`. Then `ĉ(x)(a) = 0`. Every sign functional `φ` is
  `T ↦ (T ·)(1)` for some such `T` (`exists_frobenius_intertwiner`), and
  `φ(ĉ(x)(a) v) = ((x · T) v)(1) = 0` by `eval_one_act_psAct`. The sign functionals separate
  points (`eq_zero_of_signFunctional`).
- `act_T0_eq_zero_of_kill` (**killing `T₀`**): let `V` be irreducible with
  `IsRealGKModule n ρ π`, let the Gelfand elements act by scalars `λ_l`
  (`envelopingAction π (Cgel n l) = λ_l`), and let `T₀ ≠ 0` be a `K`-intertwiner from `τ` into
  `V`. Suppose `b ∈ Bsub τ` kills every `K`-intertwiner from `τ` into `PS a e`, for every `e`
  and every `a` of the fibre `{ξ_l(a) = λ_l}`. Then `b · T₀ = 0`. Otherwise, by simplicity and
  averaging (`exists_act_eq_of_irreducible`, `act_avg`, `avg_mem_Bsub`), there is
  `x = avg(c) · b ∈ Bsub τ` with `x · T₀ = T₀`. Since `ĉ(x) = ĉ(b) ĉ(avg c)` vanishes on the
  fibre (`chat_mul`, `chat_eval_eq_zero_of_kill`), `x^m · T₀ = 0` for some `m`
  (`exists_pow_act_eq_zero`). This contradicts `x^m · T₀ = T₀ ≠ 0`.
- `exists_subquotient_of_kill` (**graph argument**): let `V` be irreducible, `T₀ ≠ 0` a
  `K`-intertwiner from `τ` into `V`, and `S₀` a `K`-intertwiner from `τ` into `PS a e`.
  Suppose every `b ∈ Bsub τ` with `b · S₀ = 0` satisfies `b · T₀ = 0`. Then there are
  `W ≤ PS a e` and a surjective `T : W →ₗ V` with `IsRealSubquotientMap n ρ π W T`. Proof:
  - Let `Z ⊆ PS a e × V` be the range of `w ↦ (Φ_{S₀}(w), Φ_{T₀}(w))` on `U(𝔤)^d`. It contains
    every `(P(u) S₀ x, π(u) T₀ x)`, and it is stable under `O(n)` (via
    `rho_mul_envelopingAction`) and under `𝔤`.
  - `Z ∩ (0 × V) = 0`. The set `{v : (0, v) ∈ Z}` is a `(𝔤, K)`-stable subspace of `V`. If it
    were `V`, some matrix `c` would give `c · S₀ = 0` and `c · T₀ = T₀`. Averaging gives such a
    `K`-invariant `c` (`act_avg`), contradicting the hypothesis since `T₀ ≠ 0`. By
    irreducibility the subspace is `0`.
  - The first projection is therefore injective on `Z`. Let `W` be its image (in
    `GL_n(ℝ) → ℂ`), and let `T` be the second projection composed with the inverse. `W ≤ PS a e`.
    `T` is surjective because the second projection of `Z` is a nonzero `(𝔤, K)`-stable subspace
    containing `T₀(ℂ^d)`. The two clauses of `IsRealSubquotientMap` (right translation by
    `O(n)` and right derivatives preserve `W` and are intertwined by `T`) follow from the
    stability of `Z`.

The graph argument replaces the last step of Wallach, *Real Reductive Groups I*, 3.5.10–3.5.11,
which passes through Proposition 3.5.4 (uniqueness of the irreducible quotient with a given
`U(𝔤)^K`-module).
