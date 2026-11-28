# An idempotent from a relative splitting basis

The module `Langlands.BushnellKutzko.RelativeSplittingIdempotent` (namespace
`Langlands.BushnellKutzko.RelSplitIdempotent`) constructs, from an `𝔬_F`-lattice chain `𝓛`
normalized by a field `E` acting on `V` and an `E`-basis `w` of `V` splitting `𝓛`
(`RelSplits`), an `E`-linear idempotent `ε` of `𝔄 = 𝓛.order` whose off-diagonal corners in
`𝔄` lie in `𝔓 = End^1(𝓛)`. When the `𝔬_E`-period of the chain is at least two, `ε` is
neither `0` nor `1`.

The decomposition `V = εV ⊕ (1 - ε)V` is a two-block coarsening of the `E`-decomposition
`V = V^1 ⊕ ⋯ ⊕ V^e` subordinate to `𝔅` of C. J. Bushnell and P. C. Kutzko, *The admissible
dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
(5.5.1)–(5.5.2), printed p. 181 (PDF page = printed page + 12): the first summand `V^1` (the
lines on which the chain jumps between `L_0` and `L_1`) against the sum of the others. The
coarsening need not itself be subordinate in the sense of (7.1.1), printed p. 208 (for
`e = 3` it has two blocks, while the number of blocks of a subordinate decomposition divides
`e`). The property that the off-diagonal corners of `𝔄` lie in `𝔓` corresponds to (7.1.15),
printed p. 213, for the subordinate decomposition and persists under the grouping, since each
corner across the grouping is a sum of off-diagonal corners; the module proves it directly
from the jumps of the chain on the lines of the basis (`offDiagonal_mem`).

## Construction

- `jumpFinset 𝓛 w`: the indices `k` such that some `c • w_k` lies in `L_0` but not in `L_1`
  (`mem_jumpFinset`).
- `projection 𝓛 w : V →ₗ[E] V`: `v ↦ Σ_{k ∈ jumpFinset} w.repr v k • w_k`, and
  `blockIdempotent 𝓛 w`, the same map as an `F`-linear endomorphism
  (`projection_apply`, `blockIdempotent_apply`, `projection_basis`,
  `sub_blockIdempotent_apply`).
- `isIdempotentElem`, `blockIdempotent_smul` (`E`-linearity),
  `blockIdempotent_mem`, `blockIdempotent_mem_order` (`ε ∈ 𝔄`, using `term_mem`: for a
  relative splitting basis each term of a lattice vector lies in the lattice).

## Jumps

Assume `𝔬_E` is a discrete valuation ring with fraction field `E`, `ϖ` a uniformizer of
`𝔬_E`, and let `uniformizerShift hE hϖ` be the shift `p` of the chain under multiplication
by `ϖ` (`ϖ L_i = L_{i+p}`).

- `inv_integral_or_dvd`: a nonzero `t ∈ E` has `t⁻¹ ∈ 𝔬_E` or `t ∈ ϖ 𝔬_E`.
- `smul_mem_succ_of_jump`: if `y ∈ L_i \ L_{i+1}` and `i + 1 ≤ i' < i + p`, then every
  `t • y ∈ L_{i'}` lies in `L_{i'+1}`: a line jumps at most once in a window of length `p`.
- `zpow_smul_mem_iff`: `ϖ^q • v ∈ L_{j + q p} ↔ v ∈ L_j`.
- `jump_line_mem_succ`: on a line of `jumpFinset`, the chain does not jump at indices not
  divisible by `p`; `nonjump_line_mem_succ`: on the other lines it does not jump at
  multiples of `p`.
- `blockIdempotent_mem_succ`: if `p ∤ i` then `ε L_i ⊆ L_{i+1}`;
  `sub_blockIdempotent_mem_succ`: if `p ∣ i` then `(1 - ε) L_i ⊆ L_{i+1}`.
- `offDiagonal_mem`: for `x ∈ 𝔄`, `ε x (1 - ε)` and `(1 - ε) x ε` lie in `𝔓`.
- `blockIdempotent_ne_zero` (from `L_1 ⊊ L_0`) and `blockIdempotent_ne_one` (from
  `L_2 ⊊ L_1` when `p ≥ 2`).
