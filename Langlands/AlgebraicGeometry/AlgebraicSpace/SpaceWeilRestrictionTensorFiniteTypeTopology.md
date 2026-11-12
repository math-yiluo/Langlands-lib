# Finite-type geometry for the tensor Weil point homeomorphism

This internal construction discharges the factor algebraicity and geometric
premises of the tensor field comparison for a quasi-separated finite-type
algebraic space. Algebraicity of the original Weil restriction remains
explicit.

Let `R` and `B` be commutative rings with a specified `R`-algebra structure
on `B`. Let `C` be a nontrivially normed `R`-algebra field, and let `D i`
be a finite family of nontrivially normed fields, each a finite-dimensional
`C`-algebra with continuous scalar multiplication and its module topology.
Each factor also has its
specified original `B`-algebra structure. A given `C`-algebra equivalence
`C tensor_R B ≃ product D i` must send `1 tensor b` to the original image
of `b` in every factor.

Let `X` over `B` be quasi-separated and of finite type, and assume that its
Weil restriction over `R` is algebraic. Assume that `C` and all `D i`
satisfy `IsHenselianValuedField`.

`WeilRestrictionTensorTopology.finiteTypeTensorPointHomeomorph`
identifies the original Weil space evaluated at `C` with the product
of the original `X(D i)`. The source has the original field-valued topology
and the target has the product of the original field-valued topologies.
Its forward components are exactly
`completedTensorSpaceWeilRestrictionPointMap`. The final theorem states
the homeomorphism property for that already defined map.

The implemented proof composes the published diagonal and affine etale
atlas theorems through `spaceWeilRestriction_of_geometricInputs`.
This supplies the full finite-projective Weil representability and
finite-type theorem without an additional mathematical premise.
Base change preserves quasi-separatedness and finite type, so the base
change of `X` to the product ring and all its factor spaces have those
properties. Each factor field is a projective `C`-module because it is
free; the finite product is also finite projective over `C`. Apply the
Weil theorem to that product and separately to each factor to obtain
algebraicity, quasi-separatedness, and finite type of the required Weil
spaces. Forgetting quasi-compactness from the finite-type atlases gives
their locally finite-type hypotheses. These inputs instantiate
`tensorPointHomeomorph`, whose component formula gives the formula here.

The provenance is internal composition of published representability,
base-change stability, and tensor topology constructions. No separability
assumption is used. The independent field norms, continuous scalar multiplication,
finite-dimensional module topology, and henselian conditions remain explicit; they are not asserted for every
incomplete henselian field extension. Arithmetic specialization and the
adelic endpoint remain outside this unit.

The scalar-action hypothesis is generalized from `NormedAlgebra` to
`Algebra` plus `ContinuousSMul`. The geometry argument is unchanged,
and the tensor topology comparison uses the original continuous
coefficient maps without requiring their preservation of the field norms.
