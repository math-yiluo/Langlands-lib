# The combinatorics of Arthur's partition lemma

Module `Langlands.LinearAlgebra.ArthurCombinatoricsPartition`, namespace
`Langlands.ArthurCombinatorics`. The objects are those of `Langlands.LinearAlgebra.ArthurCombinatorics`
(see its Markdown): a crystallographic root system `P` over `ℝ` with a base `b`, standard parabolic
subgroups recorded by subsets `Θ ⊆ b.support`, the weights `weightCoordinate`, the projection
`levelProjection` and Arthur's `tau`.

Source: J. Arthur, *A trace formula for reductive groups I* (1978), registered as
`arthur-1978-trace-formula-reductive-groups-I`, Lemma 6.3 (p.940) and the proof of Lemma 6.4
(pp.941–942).

## Results

- `weightSum b`: the sum `∑_k ϖ_k` of the fundamental weights of `b`, as an element of the weight
  space; `toLinearMap_weightSum_coroot`: it takes the value `1` on every simple coroot.
- `corootValue_weightSum_pos`: for `Θ_Q ⊆ b.support` and `i ∈ b.support ∖ Θ_Q`, the value of
  `weightSum b` on the projection of `α_i^∨` to `𝔞_Q` is positive. The projection is
  `α_i^∨ − ∑_{j ∈ Θ_Q} ϖ^Q_j(α_i^∨) α_j^∨`, and `ϖ^Q_j(α_i^∨) ≤ 0` (the published
  `weightCoordinate_coroot_nonpos`), so the value is at least `1`.
- `existsUnique_weight_nonpos_tau`: for `Θ_Q ⊆ Θ_P ⊆ b.support` and every `H` there is exactly one
  `Θ_R` with `Θ_Q ⊆ Θ_R ⊆ Θ_P`, `ϖ^R_i(H) ≤ 0` for every `i ∈ Θ_R ∖ Θ_Q` and `τ_R^P(H) = 1`.
  This is Langlands' combinatorial lemma (Arthur 1978, Lemma 6.3, published as
  `langlandsCombinatorial_eq`) with `Λ = weightSum b`: then every sign `ε_Q^R(Λ)` is `1`, every
  `φ_Q^R(Λ, H)` is the characteristic function of `{ϖ^R_i(H) ≤ 0, i ∈ Θ_R ∖ Θ_Q}`, and the sum of
  the `{0, 1}`-valued terms is `1`.
- `root'_pos_of_weight_nonpos_of_tau`: if `ϖ^{P_1}_j(H) ≤ 0` for every `j ∈ Θ_1` and
  `τ_{P_1}^P(H) = 1`, then `α_i(H) > 0` for every `i ∈ Θ_P ∖ Θ_1`. Write
  `H = H_{P_1} + ∑_{j ∈ Θ_1} ϖ^{P_1}_j(H) α_j^∨`; the first term gives `α_i(H_{P_1}) > 0` and each
  other term is a product of two nonpositive numbers. This is the step "it follows that
  `α(H_0(δ_i x) − T) > 0` for every `α ∈ Δ_0^P ∖ Δ_0^{P_i}`" of Arthur's proof.
- `levelProjection_eq_zero_of_mem_corootSpan`, `tau_add_of_mem_corootSpan`: `H ↦ H_P` vanishes on
  `𝔞_0^P`, so `τ_R^P(H + Z) = τ_R^P(H)` for `Z` in the coroot span of `Θ_R`.
- `eq_of_weight_nonpos_of_tau`: let `Θ_1, Θ_2 ⊆ Θ_P` and `H_1, H_2` with `ϖ^{P_a}_j(H_a) ≤ 0` for
  `j ∈ Θ_a` and `τ_{P_a}^P(H_a) = 1`. If `H_2 − H_1` lies in the coroot span of `Θ_1 ∩ Θ_2`, then
  `Θ_1 = Θ_2`. Both `Θ_1` and `Θ_2` satisfy the condition of `existsUnique_weight_nonpos_tau` for
  `Θ_Q = Θ_1 ∩ Θ_2` and `H = H_1`: the weights `ϖ^{P_2}_i`, `i ∉ Θ_Q`, and `τ_{P_2}^P` do not see
  the coroots of `Θ_Q`. This is the end of Arthur's "at most one" argument.
- `mem_corootSpan_inter`: the coroot spans of `Θ_1` and `Θ_2` meet in the coroot span of
  `Θ_1 ∩ Θ_2`, by the coordinates in the basis of simple coroots.
