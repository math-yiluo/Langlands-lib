# Reduction of the Tits cocycle presentation to special-linear automorphisms

This internal composition proves
`SpecialLinearTorusAutomorphismStatement` implies the exact published
`SpecialLinearTitsCocycleStatement`, in the same arbitrary universe. The
automorphism proposition remains an explicit premise; the unconditional Tits
cocycle theorem is not proved by this unit.

`Presentation.HasTitsMatrixFormulas p x` is the predicate that the family of
matrices `x` satisfies both discrepancy formulas on all relative test schemes,
classified by the original Tits star action for every supplied Galois lift.
Its maps, group-scheme local isomorphism, coefficient maps, matrix inverses and
quantifiers are the first clause of the published target, specialized to the
retained coordinate presentation `p`.

`hasTitsMatrixFormulas_discrepancyMatrices` applies the conditional all-test
matrix formulas from `SpecialLinearTitsCocycleMatrixFormulas`. The two
equivalences proved in `SpecialLinearTitsCocycleStarComparison` convert
fixedness and movement of the original star action into fixedness and movement
for the based projection of the actual discrepancy. These supply the two
case premises without changing the chosen matrices.

`specialLinearTitsCocycle_of_torusAutomorphism` constructs the finite Galois
coordinate presentation using the simply-connected and numbered type-A
hypotheses. It chooses the conditional discrepancy matrices and the already
constructed diagonal characters. The preceding comparison supplies the first
clause of the target, while `Presentation.diagonal` and
`Presentation.rootRestriction_diagonalWeights` supply the second and third
clauses. The actual finite extension, embedding, local group-scheme
isomorphism, original maximal split torus and original Tits star action are
retained. The absolutely-almost-simple premise is accepted by the target but
is not needed by this reduction.

The provenance is the composition of these internal Library interfaces; no
new original-literature result is asserted. There is no restriction on
characteristic or rank, including characteristic two and ranks zero and one,
and no downstream outer-type-A or Kneser--Tits result is used.
