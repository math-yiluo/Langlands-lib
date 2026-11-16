# The Hom bound for lower Verma modules of `𝔤𝔩_n(ℂ)`

Module `Langlands.Representation.Archimedean.LowerVermaHomBound`, namespace
`Langlands.Archimedean.VermaPBW`. It imports `LowerVermaFiltration` (and through it `LowerVermaPBW`).

The main result is `lowerVermaHomBound : VermaGL.LowerVermaHomBoundStatement.{uW}`. The
statement is in the Library module `LowerVerma`. Let `λ` be `Z`-extremal and let `σ` be a
finite-dimensional representation of `𝔤𝔩_n(ℂ)` on `W` with integral weights. Then every
linearly independent family `g : Fin d → (W →ₗ End M⁻(λ))` of equivariant maps
(`g_i(σ(Y) w) = action(Y) g_i(w) - g_i(w) action(Y)`) has `d ≤ dim W₀`
(Bernstein–Gelfand 1980, 1.9(f), 1.11(c)).

The proof does not use Verma flags or tensor products. It works in
`H = Hom(W, M⁻(λ)) ≅ W* ⊗ M⁻(λ)`, filtered by subrepresentations whose successive quotients
are quotients of lower Verma modules. Each filtration step adds at most one dimension of
singular vectors of weight `λ`, and only at a weight-zero vector of `W`. The central character
and the `Z`-extremality of `λ` rule out the other steps.

## 1. Tools from `LowerVermaFiltration`

The proof uses these generic results from `LowerVermaFiltration`:

* weights: `IsWt`, `rootOf`, `shiftOf`, `isWt_env_W`, `isWt_unique`;
* invariant subspaces: `IsInv`, `env_mem`, `env_W_mem`, `isInv_span`;
* singular vectors modulo an invariant subspace: `env_ideal_mem`;
* central characters: `center_smul_gen`, `env_center_sub_mem`;
* weight separation: `mem_span_wt`;
* weight bases: `exists_weight_basis`, `wtC`, `htZ`, `htZ_lt_of_wtC_eq`,
  `wtC_eq_of_lower_coeff`, `eq_nil_of_shiftOf_eq_zero`;
* `shiftOf_mem_posRootCone`.

## 2. The representation on `Hom(W, M⁻(λ))` (section `HomSpace`)

* `rhoH n λ σ`: `(Y · G)(w) = Y · G(w) - G(σ(Y) w)`. This is the Library's `BGChase.homLie σ
  (action n λ)`. `rhoH_apply`.

## 3. The filtration (section `Filtration`)

Fix a weight basis `b` with integer weights `m` (`exists_weight_basis`).

* `eq_sum_smulRight`: `G = Σ_j b_j^* ⊗ G(b_j)` (the Library's `BGChase.eq_sum_coord_smulRight`). `rhoH_smulRight`: the action of `E_c` on
  `b_j^* ⊗ x`.
* `Gk n λ b k = b_k^* ⊗ gen`. `isWt_Gk`: it has weight `λ - wt(b k)`. `rhoH_Gk_lower`: for
  `q < p`, `E_pq · G_k = -Σ_i (b_k^*(σ(E_pq) b_i)) G_i`. Only `i` with
  `wt(b k) = wt(b i) + (ε_p - ε_q)` occur (`wtC_eq_of_lower_coeff`), and these have larger
  height (`htZ_lt_of_wtC_eq`).
* `gensT T` is the set of vectors `E_{c₁} ⋯ E_{c_r} · G_j` with `j ∈ T`, and `FT T` is its span.
  These are abbreviations of the generic `gensG` and `FG` of `LowerVermaFiltration` for the
  family `G_j`. `isInv_FT`, `isWt_gensT`, `FT_mono` and `Gk_mem_FT` are the corresponding
  generic lemmas: invariance, weight vectors and monotonicity.
* `smulRight_W_mem_FT`, `smulRight_mem_FT`, `FT_univ`: `FT univ = H`. The vector
  `b_j^* ⊗ (W(l) · gen)` lies in `FT univ` by induction on `l`, using `rhoH_smulRight`. These
  vectors span `H`.

## 4. The step (section `Step`)

`Ssing n λ σ` is the subspace of `G ∈ H` with `E_pq G = 0` for `q < p` and weight `λ`. Fix
`k ∈ T` such that every `j` of larger height than `k` lies in `T`, and put `T' = T ∖ {k}`.

* `rhoH_Gk_lower_mem`: `E_pq G_k ∈ FT T'` for `q < p`, by the last items of §3. So
  `G_k` is singular of weight `λ - wt(b k)` modulo `FT T'`.
* `env_lower_mem`: words in lower letters map `G_k` into `FT T' + ℂ G_k`.
* `Pk k` (the generic `PG`) is the span of the `E_{c₁} ⋯ E_{c_r} · G_k` with all `c_i`
  strictly upper. `env_mem_sup`: every `u · G_k` lies in `FT T' + Pk k`. `FT_le_sup`:
  `FT T ≤ FT T' + Pk k`. These three are `envG_lower_mem`, `envG_mem_sup` and `FG_le_sup` of
  `LowerVermaFiltration`.
* `step`: if `x ∈ Ssing ∩ FT T`, then `x ∈ FT T' + ℂ G_k`, and `x ∈ FT T'` if `wt(b k) ≠ 0`.
  - By `mem_span_wt` applied to the weight-vector spanning set of `FT T' + Pk k`, `x` lies in
    `FT T'` plus the span of the upper words `w · G_k` of weight `λ`. Such a nonzero vector has
    `shiftOf(w) = wt(b k)`.
  - If `wt(b k) = 0`, only the empty word occurs.
  - If `wt(b k) ≠ 0` and such a word exists, then `wt(b k) ∈ Q₊`. So `μ = λ - wt(b k)` lies
    in `λ - Q₊` and `μ ≠ λ`. `Z`-extremality gives a central `z` and scalars `c ≠ c'` with
    `z • gen λ = c • gen λ` and `z • gen μ = c' • gen μ`. Now `z x = c x` (`x` is singular of
    weight `λ`), while `z y ≡ c' y` modulo `FT T'` for every `y` in the span of the
    `w · G_k` (`G_k` is singular of weight `μ` modulo `FT T'`, and `z` is central). Writing
    `x = f + y` gives `(c - c') x ∈ FT T'`, so `x ∈ FT T'`.

## 5. Counting (section `Count`)

* `count`: for every upward closed `T` (closed under passing to larger height),
  `Ssing ∩ FT T` is finite-dimensional, of dimension at most `#{k ∈ T : wt(b k) = 0}`. The
  proof is by strong induction on `T`, removing an element `k` of minimal height. If some
  `x₀ ∈ Ssing ∩ FT T` is not in `FT T'`, then `wt(b k) = 0` by `step`, and
  `Ssing ∩ FT T ≤ (Ssing ∩ FT T') + ℂ x₀`. Indeed, write `x = f + a G_k` and
  `x₀ = f₀ + a₀ G_k` with `a₀ ≠ 0`. Then `x - (a/a₀) x₀ ∈ Ssing ∩ FT T'`.
* `card_zero_le_finrank`: the `b k` of weight `0` are linearly independent elements of
  `zeroWeightSpace σ`.

## 6. Equivariant maps and the conclusion

* `equivSub n λ σ` is the subspace of equivariant `g : W → End M⁻(λ)`. `evalGen` is
  `g ↦ (w ↦ g(w) gen)` (`evalGen_apply`).
* `rhoH_evalGen`: `(Y · evalGen g)(w) = g(w)(Y · gen)` for equivariant `g`. Hence
  `evalGen_mem_Ssing`: since `gen` is singular of weight `λ`, so is `evalGen g`.
* `eq_zero_of_evalGen`: an equivariant `g` with `g(w)(gen) = 0` for all `w` vanishes. By
  equivariance `g(w)(E_c m) = E_c g(w)(m) - g(σ(E_c) w)(m)`, so `g(w)` kills every
  `W(l) · gen` by induction on `l`, and these span `M⁻(λ)`.
* `linearIndependent_evalGen`: `evalGen ∘ g` is linearly independent, because `evalGen` is
  injective on the span of the `g_i`, which consists of equivariant maps.
  `finrank_le_of_equivariant`: hence `d ≤ dim Ssing`.
* `lowerVermaHomBound`: `d ≤ dim Ssing = dim (Ssing ∩ FT univ) ≤ #{k : wt(b k) = 0} ≤ dim W₀`,
  by `count` with `T = univ`, `FT_univ` and `card_zero_le_finrank`.

## Provenance

The statement is the Hom bound of BG 1.9(f) and 1.11(c) (J. N. Bernstein and S. I. Gelfand,
*Tensor products of finite and infinite dimensional representations of semisimple Lie
algebras*, Compositio Math. 41 (1980); literature id
`bernstein-gelfand-1980-tensor-products`), for lower Verma modules of `𝔤𝔩_n(ℂ)`. BG pass to
`Hom(M, W* ⊗ M)` and use the Verma flag of `W* ⊗ M`. The proof here works directly in
`Hom(W, M)`. It uses only the following ingredients:

* quotients of Verma modules (`env_ideal_mem`);
* the scalar action of the center on `M⁻(μ)` (`lowerVermaWeight`);
* the weights of upper words.
