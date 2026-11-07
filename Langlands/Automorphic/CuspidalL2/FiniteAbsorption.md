# Representatives of adelic block matrices and absorption of their finite parts

Helpers for the rapid-decay argument (`Langlands.Automorphic.CuspidalL2.Decay`).
Provenance: internal; this is the standard reduction of an adelic unipotent
variable modulo rational points to a compact box, together with a finite-index
argument for open subgroups.

## Contents

- `exists_adele_decomposition K hδ z`: for a nonzero natural number `δ`, every adele
  `z` can be written `z = ξ + δ * w` with `ξ ∈ K` (embedded diagonally) and `w` in the
  compact box `archimedeanFundamentalSet K × integralFiniteAdeles K`.
  Proof: apply the Library facts `exists_sub_mem_integralFiniteAdeles` (finite part)
  and `exists_sub_integer_mem_archimedeanFundamentalSet` (archimedean part) to
  `z / δ`, and multiply back by `δ`.
- `exists_matrix_decomposition K hδ Y`: the entrywise version for a block matrix
  `Y` of adeles: `Y = ξ.map (algebraMap K _) + δ • W` with every `W i j` in the box.
- `exists_nsmul_conj_blockUnipotent_mem K n h L hL hQ` (**finite absorption**): if `L`
  is an open subgroup of the finite adelic group and `Q` is compact, then some
  natural number `δ ≠ 0` has the property that for every block matrix `W` with
  integral finite-adele entries and every `q ∈ Q`, `q⁻¹ u(δ • W) q ∈ L`.
  Proof: the set `V` of blocks `W` with `q⁻¹ u(W) q ∈ L` for all `q ∈ Q` is an
  additive subgroup (`u` is additive in the block); it is open, because the
  conjugation map is continuous and `Q` is compact (a tube-lemma
  neighbourhood of `0`). The integral blocks form a compact additive subgroup `O`, so
  `V ∩ O` has finite index in `O`; `δ` is that index, and `δ • W ∈ V` for `W ∈ O`
  by `AddSubgroup.nsmul_index_mem`.
