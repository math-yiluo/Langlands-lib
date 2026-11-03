# Full-character-kernel affine quotient specialization

This internal construction specializes the existing affine cocycle-orbit
quotient adapter to the actual full-character-kernel centralizer.
It works over any field `k` in an arbitrary universe, for a split torus `S`,
any group scheme `G`, any homomorphism `i : S.toGrp ⟶ G`, and any character
`a` of `S`. The character need not be nonzero or primitive.

`kernelDiagonalizableAction` restricts the actual conjugation action first
to `characterKernel a`, then along the inverse of
`Diagonalizable.kernelDiagonalizableIso S hS a`. Thus its acting group has
the full quotient character group `Diagonalizable.quotientLattice a`.
The published isomorphism retains torsion and the full scheme-theoretic
kernel, including nonreduced kernels.

`kernelDiagonalizableAction_fixedSubgroup` uses the published
`AutomorphicAction.fixedSubgroup_restrict_iso` theorem to identify the
resulting fixed subgroup functor with `kernelCentralizer i a`. This is
equality on all scheme tests, with fixedness after every refinement.
`kernelDiagonalizableAction_isRepresentedBy` consequently transports
the representation premise while retaining the same group `C` and
homomorphism `j : C ⟶ G`.

For smooth affine `G`, the quotient constructor takes an actual cocycle
model for this action, an actual affine orbit `O`, and a factorization
`p ≫ e = M.orbit` with `e` monic and `p` smooth and surjective.
It applies `CocycleModel.affineHomogeneousQuotientOfOrbit` with the
transported representation premise. The resulting imported
`HomogeneousQuotient j` uses exactly `O` and `p`, and has the exact
right-coset fibers on every scheme test. Its affineness theorem refers
to that same quotient, using the supplied affineness of `O`.

The companion `Torus.DiagonalizableGeometry` module supplies affine and
locally finite-type structure maps for diagonalizable groups whose full
character groups are finitely generated. The existing
`Diagonalizable.quotientLattice_fg S hS a` theorem supplies that finite
generation for this action.

No cocycle-model existence, affine-orbit existence, action-relation
smoothness, or reductivity result is asserted here. Those remain
substantive prerequisites for the exact
`KernelCentralizerComponentReductiveStatement`.
