# Absolute Hilbert 90 in characteristic zero

`AbsoluteH1Vanishing` states that the existing `absoluteCohomology K 1`
is a subsingleton for every characteristic-zero field `K`, in any carrier
universe. This is Mathlib's actual continuous cohomology of the absolute
Galois group with the discrete algebraic-closure unit representation, using
the project's lifted integer scalars. Since the cohomology is an additive
group, the subsingleton assertion means that every class is zero.

The scope covers the absolute H¹ clause of `CohomologyExistence` for every
finite extension of every p-adic field. The statement assumes no local
class formation, cohomological vanishing, or comparison isomorphism.
It asserts no H² result and does not alter the finite-relative H¹ target.

This is an internal derived target: finite Hilbert 90, the identification
of fixed units with units of the fixed field, and the finite-stage
description of continuous cohomology provide its intended proof.
Characteristic zero ensures that the algebraic closure is a Galois
extension of the base. Removing that restriction or replacing the
algebraic closure with a separable closure is outside this target's scope.
The definition itself contains no proof.
