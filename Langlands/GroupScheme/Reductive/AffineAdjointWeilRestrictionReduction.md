# The exact affine adjoint Weil target reduced to three structural inputs

The generic pair-descent statement is in `AffineWeilPairEtaleDescentStatement`
and the uniqueness construction in `WeilFactorUniquenessReduction`.

`affineAdjointWeilRestriction_of_inputs` constructs the unchanged
published `Langlands.GroupScheme.AffineAdjointWeilRestrictionStatement.{u}`
from three explicit inputs:

- actual adjoint almost-simple Weil presentations of all supplied
  adjoint pinned models with nontrivial geometric fibres;
- `AffineWeilPairEtaleDescentStatement.{u}`;
- `WeilFactorIdempotentRigidityStatement.{u}`.

This is a conditional reduction. It does not prove those three inputs
and is not an unconditional proof of the final target.

For existence, the implemented proof applies
`AffineAdjointWeilPresentation.ofPinnedCharts` to the original
reductive group, its adjoint geometric fibres and its nontrivial
geometric fibres. That construction uses the proved pinned atlas,
the supplied local presentations and generic pair descent, recovering
adjointness through the original local finite-base comparisons.
Its `exists_pair` theorem is exactly the required existential output.

For uniqueness, the two supplied comparisons from the original group
give an isomorphism of the two actual Weil restrictions. The proof
applies
`WeilFactor.exists_baseChange_iso_of_weilRestriction_iso`, supplying
factor rigidity, reductivity and the almost-simple part of the two
geometric-fibre assumptions. That theorem produces the algebra
isomorphism in the target's direction and the required actual
base-change group isomorphism.

The result treats every universe `u`, every commutative base ring
including the zero ring, and every group satisfying the unchanged
target's hypotheses. It adds no further group or base conditions.
The target's Lean/Markdown pair and its imports remain unmodified.
The source motivation is Brian Conrad, *Reductive group schemes*
(2014), Proposition 6.4.4 and Remark 6.4.5, pp.232–233, registered as
`conrad-2014-reductive-group-schemes`. The implementation is the
documented internal composition above.
