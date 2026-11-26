# Arthur's partition lemma from the reduction-theoretic lemma

Module `Langlands.Global.ArthurSiegelPartitionProof`, namespace `Langlands.Global.ArthurTruncation`.
It proves the predicates `IsSiegelPartition` and `IsRelativeSiegelPartition` of
`Langlands.Global.ArthurSiegelSetsStatement` for one compact subgroup `K` with
`P_0(𝔸)K = G(𝔸)`, from the predicate `IsSiegelReductionLemma` of
`Langlands.Global.ArthurSiegelSetsIwasawaStatement` and from `ParabolicSpacesComparisonStatement`,
and deduces `IwasawaSiegelPartitionStatement` from `IwasawaSiegelReductionStatement`.

Source: J. Arthur, *A trace formula for reductive groups I* (1978), registered as
`arthur-1978-trace-formula-reductive-groups-I`, Lemma 6.4 and its proof (pp.941–942); J. Arthur,
*An introduction to the trace formula* (2005), in
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, Lemma 8.2 (p.38) and (8.1) (p.40).
The Lean proof follows Arthur's.

## Siegel sets

- `height_siegel_product`: `H_0(n m a k) = H_0(a)` for `n ∈ N_0(𝔸)`, `m ∈ M_0(𝔸)^1`, `a ∈ A_0`,
  `k ∈ K` (the unipotent factor has no character, `m` has norm one, `H_0` is right `K`-invariant).
- `siegelSet_mono`: `S^P(T_1, ω) ⊆ S^{P_1}(T_1, ω)` for `P_1 ⊆ P`.
- `mem_siegelSet_of_mem_of_pos`: a point of `S^{P_1}(T_1, ω)` with `α(H_0(x) − T_1) > 0` for
  `α ∈ Δ_0^P ∖ Δ_0^{P_1}` lies in `S^P(T_1, ω)`.

## Translation to the abstract combinatorics

`weight_eq_weightCoordinate`, `eval_eq_root'` and `toCorootSpan_mem_corootSpan` express Arthur's
weights, the simple roots and the coroot spans of `Langlands.GroupScheme.ArthurRelative` through the
root system `ArthurRelative.rootPairing` and its base, where the results of
`Langlands.LinearAlgebra.ArthurCombinatoricsPartition` apply.

## The two halves of Lemma 6.4

Fix compact factor data `C` with `C.compactSubgroup = K`, `T_1`, and `T` with
`β(T_1) < β(T)` for every `β ∈ Δ_0` and the conclusion of `IsSiegelReductionLemma` at `T`.

- `exists_partition_term` ("at least one"): for `y ∈ S^P(T_1, ω)` there is `P_1 ⊆ P` with
  `F^{P_1}(y, T) = 1` and `τ_{P_1}^P(H_0(y) − T) = 1`: take the unique `P_1` of
  `existsUnique_weight_nonpos_tau` for `H_0(y) − T`; then `y` itself lies in the truncated Siegel
  set `S^{P_1}(T_1, T, ω)`.
- `exists_translate_of_partition_term`: if `F^{P_1}(y, T) τ_{P_1}^P(H_0(y) − T) = 1`, some
  `r ∈ P_1(F)` puts `ry` in `S^{P_1}(T_1, T, ω)`; `τ_{P_1}^P` is unchanged (`height_sub_mem_span`),
  `α(H_0(ry) − T) > 0` for `α ∈ Δ_0^P ∖ Δ_0^{P_1}` (`root'_pos_of_weight_nonpos_of_tau`), and so
  `ry ∈ S^P(T_1, ω)` since `T − T_1` is in the positive chamber.
- `partition_term_unique` ("at most one"): if the terms for `(P_1, δ_1)` and `(P_2, δ_2)`,
  `δ_a ∈ P(F)`, are `1`, translate as above to `y_a = r_a δ_a x ∈ S^P(T_1, ω)`. The
  reduction-theoretic lemma, applied to `y_1` and `δ = (r_2δ_2)(r_1δ_1)⁻¹` and to `y_2` and `δ⁻¹`,
  gives `δ ∈ P_1(F) ∩ P_2(F)`; hence `H_0(y_2) − H_0(y_1)` lies in the coroot span of
  `Δ_0^{P_1} ∩ Δ_0^{P_2}`, and `eq_of_weight_nonpos_of_tau` gives `P_1 = P_2`. Then
  `δ_2 δ_1⁻¹ = r_2⁻¹ δ r_1 ∈ P_1(F)`.

## The predicates

`isRelativeSiegelPartition_of_reduction` and `isSiegelPartition_of_reduction` choose
`c = |c_0| + ∑_{β ∈ Δ_0} |β(T_1)|`, with `c_0` from `IsSiegelReductionLemma` (`regular_of_lt`).
The terms are `{0, 1}`-valued, and `F^{P_1}(·, T)` and `τ_{P_1}^P(H_0(·) − T)` are left
`P_1(F)`-invariant (`siegelIndicator_mul_left`, `tau_height_mul_left`), so they do not depend on the
chosen coset representatives. For `x ∈ G(𝔸)` the covering hypothesis gives `δ_0 ∈ P(F)` with
`δ_0 x ∈ S^P(T_1, ω)` (for `IsSiegelPartition`, `P = G` and `δ_0 ∈ G(F) = P_{Δ_0}(F)`), and
`exists_partition_term` a pair `(P_0', P_0'(F)δ_0)` whose term is `1`. By `partition_term_unique`,
every pair with a nonzero term is this one. So each support is a subsingleton, hence finite, and
the double sum is `1`.

`iwasawaSiegelPartitionStatement_of_reduction` combines the two for every `K`.
