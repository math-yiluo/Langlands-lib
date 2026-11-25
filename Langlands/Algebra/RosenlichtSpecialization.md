# Rational-point and specialization tools for Rosenlicht tensor units

These internally derived helpers supply the specialization step of the algebraic
Rosenlicht tensor-unit proof. Their rational-point assertions concern finite-type
algebras over an algebraically closed field; zero detection and constancy also
use the domain hypothesis on the first algebra.

`exists_point_with_kernel` applies
`Langlands.GroupScheme.KostantRosenlicht.exists_algHom_ker_eq` from
`Langlands.GroupScheme.KostantRosenlicht.Points`. That lemma equips the
maximal-ideal quotient with its field structure and uses
`finite_of_finite_type_of_isJacobsonRing` to show that it is finite over the
ground field. It applies `IsAlgClosed.algebraMap_bijective_of_isIntegral` to
identify the quotient with the ground field. Composing the inverse isomorphism
with the quotient map gives a rational point with the prescribed kernel.
`exists_point` follows by choosing a maximal ideal in a nonzero ring.
`eq_zero_of_all_points` places an element vanishing at every rational point in
the Jacobson radical. The finite-type Jacobson property and the radicality of
the zero ideal of a domain force that element to be zero.

`specialize` evaluates the first tensor factor at a rational point; `contract`
applies a linear form to the second factor. Their pure-tensor identities give
`contract_specialize` by tensor induction. A basis of the second factor shows
that all contractions jointly detect zero tensors. Commuting contraction with
specialization and applying point detection then gives
`tensor_eq_zero_of_specialize`.

`constant_of_finite_specializations` proves that a tensor with only finitely
many specialization values is a pure tensor `1 ⊗ b`. If it differed from each
possible constant value, contraction would give one nonzero coefficient of each
difference. The product of these finitely many coefficients vanishes at every
rational point, since each point realizes one of the values. Point detection
makes this product zero, contradicting the domain hypothesis.

`exists_finite_specialization_space` bounds a tensor family's values in a
finitely generated subspace of the second factor. Tensor induction uses the
span of the second factor of a pure tensor, and the supremum of two finite
spans for a sum. `evaluateRight` evaluates the second tensor factor at a rational
point. Its pure-tensor identity and tensor induction show that the two scalar
evaluations commute. These coefficient bounds and evaluation identities are
used to normalize tensor units and their inverses in the reduction module.

The direct Mathlib imports are `Mathlib.FieldTheory.IsAlgClosed.Basic`,
`Mathlib.RingTheory.Jacobson.Ring`, `Mathlib.RingTheory.TensorProduct.Maps`,
`Mathlib.LinearAlgebra.TensorProduct.Basis`, and
`Mathlib.LinearAlgebra.Basis.VectorSpace`. The arguments work with independent
universes for the field and the two algebras.
