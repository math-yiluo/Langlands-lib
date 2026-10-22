# Smoothness of the restricted tensor product action

This module proves smoothness using the published `Langlands.IsSmooth` predicate:
each vector is fixed by an open subgroup. It imports the actual algebraic
restricted tensor product representation from `RestrictedTensor.Action` and
uses Mathlib's restricted-product topology.

For a finite elementary tensor, local smoothness supplies an open subgroup
fixing each of its finitely many coordinates. `stageOpenSubgroup` constructs
the subgroup of the restricted product whose coordinates lie in these
subgroups on that finite set and in the reference subgroups elsewhere.
The finite coordinate conditions are open by continuity of evaluation; the
outside conditions are open in the restricted-product topology. The
elementary action formula proves that this subgroup fixes the tensor.
Tensor induction then uses intersection of open subgroups for addition
and closure of fixed vectors under scalar multiplication.

The result requires only openness of the reference subgroups, so includes
the requested compact-open case. No topology, finite-dimensionality or
admissibility is imposed on the local vector spaces. Even continuity of
the local group operations is unnecessary for this open-subgroup
fixed-vector assertion; in the usual topological-group setting Mathlib
also supplies the topological-group structure on the restricted product.

This is an intrinsic proof of smoothness of the construction in Flath (1979),
section 2, printed pages 180–181, especially Example 2 on page 181
(one-based PDF page 177). Registered original:
`flath-1979-tensor-products`, Corvallis Part I, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The precise meaning of smoothness is imported from the published
`Langlands.Representation.Smooth.Definitions`; no alternate smoothness
predicate is introduced. The proof uses the actual subgroup, invariant
submodule, elementary-tensor and induction definitions.

`isSmooth_representation` handles the general direct-limit carrier.
`isSmooth_productRepresentation` specializes to the prescribed nonzero
reference-vector input. Coefficient, index, group and vector-space universes
remain independent. Neither theorem asserts automorphic factorization,
admissibility or local-factor uniqueness.
