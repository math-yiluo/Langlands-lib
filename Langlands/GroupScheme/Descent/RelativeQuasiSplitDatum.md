# Effective descent of relative quasi-split group-and-torus data

This module assembles affine ambient group descent with the descent of
supplied relative Borel and maximal-torus inclusions. Its assumptions contain
actual invariant overlap ranges; it does not construct these from a pinning.

`IsReductive.of_iso` transports relative reductivity through an actual group
isomorphism. Smoothness and affineness transport through its underlying scheme
isomorphism. Over each geometric point, the pseudo-reductive group is connected
reductive over an algebraically closed field; field-level isomorphism transport
gives the required pseudo-reductive fibre.

`IsReductive.of_baseChange` reflects reductivity under flat, surjective,
quasi-compact base change when the original group is already affine over its
base. Smoothness descends. For each base point choose an upstairs preimage.
The residue-field extension and iterated-pullback comparison identify the
upstairs connected reductive fibre with an extension of the downstairs fibre.
Field-extension reflection gives downstairs connected reductivity. Extending
this residue fibre to its algebraic closure supplies the required
pseudo-reductive geometric fibre.

`Descent.Solution.invariantRange_inv` transports a supplied invariant closed
subgroup range to the canonical datum on the actual descended ambient group.
Compatibility of the solution isomorphism identifies the two overlap actions;
postcomposition by its inverse preserves the equality of ranges.

`Descent.RelativeQuasiSplitTorusSolution` records an actual solution of the
ambient datum, affineness and reductivity of its group, an actual descended
relative Borel, an actual descended closed fibrewise maximal relative torus and
containment of the torus in the Borel. Both subgroup records retain their
pullback recovery isomorphisms and exact recovery equations.

`Descent.Datum.relativeQuasiSplitTorusSolution` constructs this record for an
étale surjection between affine bases. It takes a reductive group upstairs, a
closed relative Borel, a closed fibrewise maximal relative torus contained in
the Borel, and invariance of both ranges under the actual ambient group datum.
Effective affine group descent constructs the ambient solution. Reductivity
reflects by the preceding lemma. Transporting the inclusions along the solution
comparison gives canonical invariant subgroup data; the relative subgroup
descent constructions then provide both subgroups and their containment.

The method `RelativeQuasiSplitTorusSolution.quasiSplit` uses its constructed
relative Borel to witness relative quasi-splitness. No isomorphism with a given
downstairs group or innerness assertion is supplied by this module.

Shared declarations `IsReductive.of_iso` are imported from `Langlands.GroupScheme.NormalQuotientReductiveGluing`; their mathematical hypotheses, conclusions and data are unchanged.
