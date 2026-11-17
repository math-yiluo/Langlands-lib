# Tensor evaluation of compact and Lie intertwiners

This internal construction for Task 7294 defines tensor evaluation for
simultaneous compact and Lie intertwiners and proves its injectivity from
the published `(g,K)` Jacobson density theorem. It uses the existing
`Archimedean.gkHoms` space. No tensor surjectivity or pairing is assumed or
asserted.

For two complex vector spaces with compact-group and complex Lie algebra
actions, the multiplicity space consists of all linear maps intertwining
both actions. Evaluation sends `v ⊗ f` to `f(v)` and intertwines the source
compact and Lie actions on the first tensor factor. Simultaneous
intertwiners also commute with every noncommutative polynomial in the
compact and Lie generators, by free-algebra induction.

If the source is irreducible under the combined actions, evaluation at a
single nonzero vector is injective on the multiplicity space. The kernel
of a simultaneous intertwiner is stable under both action families. If
the intertwiner vanishes at that vector, its kernel is the whole source,
so the intertwiner is zero.

For tensor injectivity the source satisfies the existing
`GKModuleDensity.Hyp`: combined irreducibility, compact admissibility,
compact local finiteness and continuity of every scalar compact
coefficient. Express a tensor as a finite sum in a basis of the source.
For each coefficient, Jacobson density realizes a rank-one coordinate
operator on the finitely many source basis vectors occurring in the sum
by a polynomial in the action generators. Apply that polynomial to the
zero evaluation. Intertwining carries its action to the source factors,
where it isolates the chosen coefficient at any prescribed vector.
Thus each multiplicity coefficient vanishes, and so does the original
tensor. The implemented argument adapts the published finite-group-factor
tensor injectivity proof to the Library's genuine compact and Lie density
algebra.

All group, Lie algebra and carrier universes are free. The target actions
need no irreducibility, admissibility or local finiteness assumption.
