# Rosenlicht splitting of tensor units

Workers 287 and 565, 17 November 2026; submitted for Task 7617 by
Worker 5678, 18 November 2026.

`Langlands.Algebra.rosenlichtTensorUnits` proves exactly
`Langlands.Algebra.RosenlichtTensorUnitsStatement.{u,v,w}`, with three
independent universes and no additional hypotheses.

The proof combines
`Langlands.Algebra.Rosenlicht.tensorUnits_of_boundedInversePairs`, developed
by Worker 287, with
`Langlands.Algebra.Rosenlicht.boundedInversePairs`, developed by Worker 565.
The latter proves the published statement
`Langlands.Algebra.RosenlichtBoundedInversePairsStatement`, which is exactly
the bounded inverse-pair premise of the reduction. Its proof uses
homogeneous matrix equations, the algebraically closed field
Nullstellensatz and finite-dimensional coordinate algebras.

The reduction chooses rational points of the finite-type algebras. Evaluating
the tensor unit at a point of the second factor gives a unit of the first.
Dividing out this unit normalizes both the tensor and its inverse. Their
specializations lie in two finite-dimensional subspaces of the second
algebra. Bounded inverse-pair finiteness makes the specialization family
finite, and the point-detection and domain lemmas make the normalized
tensor constant. A point of the first factor identifies that constant
as a unit of the second factor. Undoing the normalization gives the
required pure tensor of units.

The direct imports are
`Langlands.Algebra.RosenlichtTensorUnitsReduction` and
`Langlands.Algebra.RosenlichtBoundedInversePairs`; their paired Markdown
describes the implemented proofs and further imports. The project modules in
the import closure are these two, `RosenlichtPolynomialFiniteness`,
`RosenlichtSpecialization`, and the two published statements
`RosenlichtTensorUnitsStatement` and `RosenlichtBoundedInversePairsStatement`
(all in `Langlands/Algebra/`); every other import is from Mathlib.
The proof does not invoke the scheme-level product-units statement.
The final theorem depends only on the axioms `propext`, `Classical.choice`
and `Quot.sound`.
