# Full-kernel centralizer quotients from geometric inputs

Author: Worker 1465.

This internal construction combines the published full-kernel action and
quotient adapters with three explicit, unproved geometric propositions. It is
uniform in an arbitrary universe `u` and an arbitrary field `k`. Its inputs are
`AutomorphicAction.AffineFiniteTypeCocycleModelStatement`,
`Diagonalizable.CocycleModelActionRelationSmoothStatement`, and
`SchemeAction.SmoothActionAffineOrbitStatement`, all at universe `u`.

For a smooth affine group scheme `G`, a split torus `S`, any homomorphism
`i : S.toGrp ⟶ G`, and any character `a`, the construction uses the full
quotient lattice `Diagonalizable.quotientLattice a`. The published
`quotientLattice_fg` theorem and `DiagonalizableGeometry` instances give a
finitely generated character group and an affine finite-type acting group.
No primitivity, nonzero character, characteristic, or perfectness assumption is
needed here. The actual conjugation action is the published
`kernelDiagonalizableAction`; it retains the full scheme-theoretic kernel,
including its torsion and nonreduced cases.

`exists_kernelCentralizerAffineQuotient_of_geometry` applies the model
existence input to this action, the smooth-relation input to that model, and the
affine-orbit input to its trivial basepoint. The model orbit is definitionally
the published scheme-action orbit of that point. The resulting orbit embedding
is monic because it is an open immersion. The existing
`kernelCentralizerAffineHomogeneousQuotient` adapter then gives an actual
`HomogeneousQuotient j` for any `j : C ⟶ G` representing the full kernel
centralizer. This quotient retains the exact right-coset fiber equation on all
scheme tests and has an affine structure morphism.

`kernelCentralizerAffineQuotientOfGeometry` chooses one such quotient, and
`kernelCentralizerAffineQuotientOfGeometry_isAffineHom` proves affineness for
that same quotient. These constructions do not need a closedness or smoothness
premise on `C`; those premises are needed by the later reductivity criterion.

`kernelCentralizerComponentReductive_of_geometry` additionally takes the
explicit input `AffineHomogeneousQuotientReductiveStatement`. It proves the
exact existing `KernelCentralizerComponentReductiveStatement` conditionally on
these four inputs. For the representative already quantified by that target,
it uses the supplied closedness and smoothness, derives its affineness, and
applies the generic reductivity criterion to the constructed quotient. The
identity component is the actual published construction of that same
representative; no comparison with a different representative is required.

The provenance is internal composition of the published interfaces. The
geometric and reductivity statements remain hypotheses: this module proves
none of those four propositions and supplies no unconditional proof of the
centralizer reductivity target. It uses no root-system, rank-one factorization,
or reflection-existence premise. The paired imported statement modules give
the original-source provenance of each remaining substantive input.
