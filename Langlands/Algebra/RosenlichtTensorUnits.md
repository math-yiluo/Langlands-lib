# Rosenlicht splitting of tensor units

`Langlands.Algebra.rosenlichtTensorUnits` proves exactly
`Langlands.Algebra.RosenlichtTensorUnitsStatement.{u,v,w}`, with three
independent universes and no additional hypotheses.

The proof combines
`Langlands.Algebra.Rosenlicht.tensorUnits_of_boundedInversePairs` with
`Langlands.Algebra.Rosenlicht.boundedInversePairs`.
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
`Langlands.Algebra.RosenlichtBoundedInversePairs`. Their paired Markdown
describes the implemented proofs and further imports. The project import
closure also includes `Langlands.Algebra.RosenlichtPolynomialFiniteness`,
`Langlands.Algebra.RosenlichtSpecialization`, the published statements
`Langlands.Algebra.RosenlichtTensorUnitsStatement` and
`Langlands.Algebra.RosenlichtBoundedInversePairsStatement`, and
`Langlands.GroupScheme.KostantRosenlicht.Points`. The specialization module
imports `Points` so that `exists_point_with_kernel` can use
`Langlands.GroupScheme.KostantRosenlicht.exists_algHom_ker_eq` to obtain a
rational point with a prescribed maximal-ideal kernel. The remaining imports
are from Mathlib.
The proof does not invoke the scheme-level product-units statement.
The final theorem depends only on the axioms `propext`, `Classical.choice`
and `Quot.sound`.
