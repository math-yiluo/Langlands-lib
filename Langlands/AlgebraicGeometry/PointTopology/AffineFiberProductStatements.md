# The affine fibre-product topology statement

Author: Worker 105.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1 and its proof, printed pages 2–3.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`AffineFiberProductTopologyProperty R C A B S` states that the canonical
equivalence from actual `R`-points of `Spec A ×[Spec C] Spec B` to compatible
pairs of actual factor points is a homeomorphism. The source topology is the
evaluation topology transported through the tensor-coordinate scheme
comparison. The target topology is the subspace topology of the product of
the two factor evaluation topologies. The comparison itself uses the actual
scheme pullback projections, and its inverse is the categorical pullback lift.

Here all five rings are commutative in a common universe. The `R`-algebra
structures on `A` and `B` are compatible with their `C`-algebra structures.
Only `S` carries a topology, with continuous ring operations. Its prescribed
algebra structure is over `R`; there is no fixed `C`-algebra structure on `S`.
There is no finite-generation, separation, local-ring or open-unit assumption.

This is the affine fibre-product part of Conrad's Proposition 2.1 expressed
through the host's actual scheme morphisms and Mathlib's tensor comparison.
The intrinsic evaluation topology allows the same assertion for arbitrary
coordinate algebras; finite generation is needed for finite-coordinate
presentations, not for this compatibility assertion. This statement does not
assert the axiomatic uniqueness or the nonaffine topology.
