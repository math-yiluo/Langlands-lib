# Actual root factors of split reductive isogenies

This internal derived construction specializes finite equivariant additive-line
root extraction to the actual root subgroups of a specified split maximal torus
of a connected reductive group over an arbitrary field.

For a finite group homomorphism `φ : G ⟶ G'` and a commuting map `t : T ⟶ T'`
of split tori, suppose root data `P` and `P'` identify their roots with
the actual adjoint roots and `P` is reduced. The target group is affine and of finite type, and the
source torus is maximal. For every source root index `r`, the construction
`IsRootDatumOf.isogenyRootFactor` chooses a target index `s` and a natural number
`n` such that

`t ≫ P'.root s = (ringExpChar k ^ n) • P.root r`.

The implemented proof first excludes higher positive multiples using reducedness
and torsion-freeness of the source character lattice. It represents the actual
source root functor by a smooth connected closed subgroup and supplies natural
coordinates of the original root weight. The intrinsic Lie-module comparison
with the source root weight space, together with the split root Lie-line
theorem, proves that those coordinates have dimension one.

Composing its closed inclusion with `φ` is finite, and the commuting square
intertwines the actual torus action with target conjugation on every test
scheme. `HomImage.exists_root_expChar_factor` then produces the target root
and exponent. The actual target root-datum equality recovers its index. The
construction uses choice only to select witnesses of this proved existence.

Provenance is internal and derived from the root-functor coordinates, actual
Lie comparisons, the split root Lie-line theorem, and the finite-line image
root extraction. This module does not prove that the chosen index map is
bijective, the coroot equations, the centrality comparison, or the full
`IsogenyRootDatumStatement`.
