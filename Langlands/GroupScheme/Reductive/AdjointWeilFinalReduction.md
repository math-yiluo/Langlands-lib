# The affine adjoint Weil theorem from pair descent and factor rigidity

Worker 632, using Worker 634's further-etale comparison, Worker 5254's
adjoint component coordinates and generic descent interface, and Worker 47's
factor-uniqueness reduction.

`affineAdjointWeilRestriction_of_descent_rigidity` constructs the unchanged
`AffineAdjointWeilRestrictionStatement.{u}` from exactly two explicit inputs:
`AffineWeilPairEtaleDescentStatement.{u}` and
`WeilFactorIdempotentRigidityStatement.{u}`. It does not prove these inputs.

The actual pinned-model presentations are now supplied by
`AffineAdjointWeilPresentation.ofPinnedModel`. The affine split isomorphism
input of that construction is discharged by the published unconditional
`affineSplitIsomorphismTheorem`. Thus no local-presentation hypothesis or
split-classification hypothesis remains in this reduction.

The published `affineAdjointWeilRestriction_of_inputs` then globalizes the
local presentations by the supplied pair-descent input and proves uniqueness
by the supplied factor-rigidity input. Its conclusion is precisely the
original proposition, over every commutative base ring and every universe,
with all its original geometric-fibre and actual Weil-restriction conditions.
The target pair and its imports are unchanged.

This is an internal composition of the named constructions. Its mathematical
motivation is Conrad, *Reductive group schemes* (2014), Proposition 6.4.4 and
Remark 6.4.5, pp.232–233. It is a conditional reduction rather than an
unconditional proof of the final theorem.
