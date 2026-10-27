# One compact open subgroup with block Iwahori factorizations for every shape

Author: Worker 246.

This module proves two neighbourhood-basis theorems. No definition or statement
is introduced.

## `GeneralLinear.BlockShape.exists_compactOpenSubgroup_forall_hasBlockIwahoriFactorization`

For every prime `p`, every `F : PadicField.{uF} p`, every `T : F.TopologicalData`
and every rank `n`, with the topology `T.topology`: every neighbourhood `U` of
`1` in `GeneralLinear n F.Carrier` contains a compact open subgroup `K` such that
`B.HasBlockIwahoriFactorization T K` holds for **every** block shape
`B : BlockShape n` simultaneously.

The published `blockIwahoriBasis` gives, for one fixed shape, a compact open
subgroup inside `U`. Its proof already uses a positive principal level subgroup,
which works for every shape at once; this module records that uniform form. The
proof repeats the published argument with the same subgroup for all shapes:

- At rank zero the whole group is trivial. `K = ⊤` is compact and lies in `U`,
  and every factorization condition holds trivially.
- At positive rank, `Conductor.exists_pos_principalLevelOpenSubgroup_subset`
  gives a positive level `a` whose principal level subgroup lies in `U`. That
  subgroup is compact (`Conductor.isCompact_principalLevelOpenSubgroup`). The
  published `principalLevelSubgroup_iwahoriProduct_bijective` gives its
  factorization for any shape. For a weakly contracting block-scalar tuple,
  conjugation preserves the upper and lower Iwahori parts. The entrywise
  congruence computation is in the private helpers
  `uniformEntryIdeal_upper_conj`, `uniformEntryIdeal_lower_inv_conj`,
  `uniformPrincipal_upper_conj` and `uniformPrincipal_lower_inv_conj`. These
  are copies of the private helpers of `Langlands.Group.GL.BlockIwahoriBasis`,
  which are not importable.

## `CuspidalSupport.exists_leviPiOpenSubgroup_subset_forall`

For a block shape `B : BlockShape n`, every neighbourhood of `1` in the product
Levi `B.Levi F.Carrier` contains a product subgroup
`CuspidalSupport.leviPiOpenSubgroup T B K`. Each factor `K j` is a compact open
subgroup of `GeneralLinear (B.size j) F.Carrier`, and it has the block Iwahori
factorization for every block shape of `B.size j`. The proof is that of the
published `CuspidalSupport.exists_leviPiOpenSubgroup_subset`, with the uniform
theorem above in place of the one-shape basis.

These results are used by the product-Levi chamber bound, which needs one
compact open subgroup with factorizations for the Borel refinement and for every
maximal refinement of each block.
