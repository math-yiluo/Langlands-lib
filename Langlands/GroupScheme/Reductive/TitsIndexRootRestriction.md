# Restricting absolute weights in an actual Tits index

This internal derived unit works over an arbitrary field `K : Type u`,
with the affine and locally finite type hypotheses of `TitsIndexData G`.
It uses the actual root datum of the supplied pinning and the actual
maximal split torus. It introduces no classification or local arithmetic
assumption.

`rootRestrictionHom` is an additive homomorphism from the character lattice
of the pinned torus over the separable closure to the character lattice
of the ground-field split torus. It first applies `TitsIndexStarProof.resK`,
restriction to the base-changed split torus. It then applies the inverse
of `characterLattice.baseChangeEquiv`, whose split-torus hypothesis is
provided by maximal splitness. Thus restriction is defined on every
absolute weight, rather than only on the indexed roots.
`rootRestrictionHom_root` identifies its value on a root with the existing
`rootRestriction`.

`rootRestriction_reflection` applies this homomorphism to the integral
root-reflection formula. For absolute root indices `a` and `b`, it proves
that the restriction of the reflection of `b` in `a` is the restriction of
`b` minus `pairing b a` times the restriction of `a`. The implemented proof
uses `root_reflectionPerm`, `reflection_apply_root`, and preservation of
subtraction and integer scalar multiplication by an additive homomorphism.

`rootRestriction_ne_nsmul_of_three_le` proves that an absolute root cannot
restrict to `n` times the restriction of a distinguished simple vertex
when `3 <= n`. The distinguished restriction is nonzero by definition and
is an actual relative root by
`TitsIndexStarProof.mem_relativeRoots_of_ne_zero`.
The split character lattice is torsion free: its canonical map into its
rationalization is injective by `character_toRat_injective`, and the
rationalization is a rational vector space. Thus the alleged multiple is
nonzero, making the other absolute restriction an actual relative root
as well. The published `relativeRootSystem` theorem supplies
`HasRelativeRootSystem` for the maximal split torus, and
`HasRelativeRootSystem.nsmul_not_mem_of_three_le` excludes the multiple.
No reducedness hypothesis is added.

The construction and proofs are derived directly from these published
interfaces. Their field, universe and characteristic scope is unchanged.
