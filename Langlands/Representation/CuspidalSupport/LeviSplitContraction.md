# Splitting one block of a product Levi and contracting its unipotent radical

This auxiliary module supplies the group-theoretic and topological facts used by
`QuasicuspidalLeviAdmissibilityProof` to turn quasicuspidality of a product-Levi
representation into vanishing of averaged translates. All declarations live in
the namespace `Langlands.CuspidalSupport.LeviAdmissibility`. They are internal
helpers derived for this proof; the corresponding classical facts are the
contraction of a unipotent radical by a dominant torus element (Bernstein and
Zelevinsky 1976, literature id `bernstein-zelevinsky-1976-representations-gln`,
the setting of §§3.20–3.26), but the formulations below are specific to the
Library's `BlockShape`, `BlockRefinement` and `Iwasawa.torus` conventions.

## Auxiliary block shapes

- `oneBlock m hm` is the block shape of the positive rank `m` with a single
  block of size `m`.
- `twoBlock m a ha`, for `a + 1 < m`, has two blocks of sizes `a + 1` and
  `m - (a + 1)`.
- `index_val` computes the numbering `B.index i b` of the coordinate `b` of
  block `i` as the sum of the sizes of the earlier blocks plus `b`;
  `twoBlock_index_fst` and `twoBlock_index_snd` specialize it to the two blocks of
  `twoBlock`.
- `SplitUnipotent m a u` says that the matrix `u` agrees with the identity
  matrix at every entry `(p, q)` outside the upper-right corner
  `p ≤ a < q`.
- `eq_one_of_mem_oneBlock_unipotent`: the unipotent subgroup of the one-block
  shape is trivial (its block-diagonal part is the identity and there are no
  off-diagonal blocks).
- `splitUnipotent_of_mem_twoBlock`: every element of the unipotent subgroup of
  `twoBlock m a ha` is split unipotent. The proof checks the four corners: the
  two diagonal blocks are the identity by the unipotent condition, and the
  lower-left corner vanishes by the parabolic condition.

## Refinements splitting one block

For a block shape `B` of rank `n`, a block `i` and `a + 1 < B.size i`,
`splitRefinement B i a ha` is the block refinement that replaces block `i` by
`twoBlock (B.size i) a ha` and every other block `j` by `oneBlock (B.size j)`.
`splitRefinement_self` and `splitRefinement_of_ne` evaluate it.

- `splitRefinement_parabolic_ne_top`: the refined parabolic
  `refinedParabolic K B (splitRefinement B i a ha)` is a proper subgroup of
  `B.Levi K` over every field `K`. If it were everything, then every element of
  `GL_{B.size i}(K)`, placed in block `i` by `Pi.mulSingle`, would lie in the
  parabolic of `twoBlock`, which would then be the whole group. The published
  lemma `block_indices_subsingleton_of_parabolic_eq_top` (module
  `JacquetVanishingSubgroups`) then forces the two blocks to coincide, which is
  false.
- `mem_splitRefinement_unipotent`: an element `u` of the refined unipotent
  radical is `1` in every block `j ≠ i`, and its block `u i` is split unipotent.

## Contraction by deep torus elements

Here `K` is a field with a valuative relation and the valuative topology.
`Iwasawa.torus ϖ lam` is the diagonal matrix `diag(ϖ ^ lam p)`.

- `tendsto_zpow_uniformizer`: for a uniformizing element `ϖ`
  (`Iwasawa.IsUniformizingElement`), `ϖ ^ z` tends to `0` as `z → ∞`. Every
  basic neighbourhood of `0` is `{x | v x < γ}`, `γ` is the value of some nonzero
  `y`, `v y = v ϖ ^ k` for some integer `k`, and `v ϖ ^ z < v ϖ ^ k` for `z > k`
  because `0 < v ϖ < 1`.
- `torus_conj_apply`: the `(p, q)` entry of `t u t⁻¹` with
  `t = Iwasawa.torus ϖ lam` is `ϖ ^ (lam p - lam q) * u p q`.
- `gapFilter m a ha` is the filter on exponent vectors `lam : Fin m → ℤ` that
  are antitone and whose gap `lam a - lam (a + 1)` tends to `+∞`.
- `tendsto_torus_conj_val`: along `gapFilter`, the matrix of `t u t⁻¹`
  tends to the identity for every split-unipotent `u`. For an upper-right entry,
  `p ≤ a < q` and antitonicity give `lam p - lam q ≥ lam a - lam (a + 1)`, so the
  factor `ϖ ^ (lam p - lam q)` tends to `0`; every other entry of `u` is an
  identity entry and is unchanged by conjugation.
- `tendsto_units_one`: a function into `GL_m(K)` tends to `1` if its matrices and
  the matrices of its inverses both tend to `1` (Mathlib's embedding of units into
  `M × Mᵐᵒᵖ`).
- `torus_conj_eventually_mem`: if `u` and `u⁻¹` are split unipotent and `O` is a
  neighbourhood of `1` in `GL_m(K)`, then there is an integer `N` such that
  `t u t⁻¹ ∈ O` for every antitone `lam` with `N ≤ lam a - lam (a + 1)`. This is
  the previous two lemmas with the filter unfolded.

## Block-diagonal torus elements

- `leviTorus B ϖ lam` is the element of `B.Levi K` whose block `j` is
  `Iwasawa.torus ϖ (lam j)`.
- `leviTorus_conj_of_eq_one`: conjugating an element supported in block `i` by
  `leviTorus B ϖ lam` gives `Pi.mulSingle i` of the conjugate of its block `i` by
  `Iwasawa.torus ϖ (lam i)`.
- `leviTorus_add_const`: adding a constant `c j` to every exponent of block `j`
  multiplies `leviTorus B ϖ μ` by the block scalar `leviTorus B ϖ (fun j _ => c j)`.
- `leviTorus_const_comm`: block scalars commute with every element of the Levi,
  because a scalar diagonal matrix commutes with every matrix.
