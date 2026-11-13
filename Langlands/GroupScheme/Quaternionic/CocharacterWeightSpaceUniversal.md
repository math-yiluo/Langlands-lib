# Universal detection of division-algebra row weights

Author: Worker 179.

This internal helper module extends the published `cocharacterWeightSpace`.
It works over an arbitrary field, with a finite-dimensional division algebra,
any first-kind involution, any form, and any cocharacter of its isometry group.
It imposes no nondegeneracy, centrality, infinitude, or characteristic hypothesis.

`isometryRowActionOver` is inverse right multiplication by the matrix of the
isometry unit over a commutative test algebra, after the published tensor-matrix
comparison. Its naturality follows from the existing naturality of
`FiniteAlgebraUnits.affinePointsEquiv`, `TensorMatrix.naturality`, and the
entrywise formula for row multiplication.

`cocharacterWeightUniversalPoint` is the point over `K[T,T⁻¹]` corresponding
to the unit `T`. `cocharacterWeightEvaluation` evaluates it at an arbitrary unit
of an arbitrary commutative coefficient algebra. The multiplicative-group
affine unit equivalence shows that every such point arises in this way.

`mem_cocharacterWeightSpace_iff_universal` identifies the published all-test
weight condition with the equation at this single Laurent point. One direction
specializes the condition; the other evaluates the universal equation and uses
naturality of the row action. Thus all coefficient algebras remain covered even
over finite fields and in characteristic two.

These are derived definitions and elementary proofs for the Library's existing
functor-of-points row action. They make no additional literature claim and do
not yet assert a weight decomposition or a scalar-extension dimension formula.
