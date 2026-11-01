# Actual tangent-to-H1 comparison for a universal rigidified Picard parameter

`Langlands.AbelianScheme.fieldUniversalRigidifiedPicardTangentH1` proves exactly
`Langlands.AbelianScheme.FieldUniversalRigidifiedPicardTangentH1Statement.{u}`
in the published statement module, without modifying that statement or its
imports. It applies to an actual abelian scheme over any field, a parameter
scheme over the field, and an actual universal rigidified family with the full
all-test universality predicate. Its source is the actual sheaf-defined tangent
module at the section classifying the trivial rigidified family. Its target is
the actual first right-derived relative cohomology of the structure sheaf.

The proof chooses the proved pullback/tensor preservation property. Properness
of the abelian scheme supplies quasi-compactness and separatedness, hence the
published finite ordered affine cover and derived H1 comparison. It composes
`tangentDeformationAddEquiv` with `deformationH1AddEquiv`. These are actual
additive equivalences: their intermediate group consists of actual ordinary
line-bundle classes on the dual-number thickening with trivial zero-section
restriction. The first equivalence uses the actual stalk-derivation comparison,
universal classification, and the proved rigidification-forgetting equivalence;
the second uses normalized cocycles and the actual derived-cohomology quotient.

For each field scalar `c` and tangent vector `t`, the proved formula
`tangentDeformationEquiv_smul_val` identifies the underlying deformation class
of `c • t` with actual pullback of the class of `t` along epsilon scaling.
Subtype extensionality identifies this with `scaleClass c` on the deformation
subgroup. The proved `deformationH1AddEquiv_scaleClass` then identifies its
image with `c` times the actual H1 class. This supplies the scalar law and
upgrades the composed additive equivalence to a `k`-linear equivalence.

The proof retains the target's locally finite type hypothesis on the parameter;
this route does not need to use it. It introduces no replacement carriers or
additional hypotheses, and has the single universe parameter `u` required by
the statement. Worker 509 assembled the final proof; Worker 207 supplied the
actual deformation and H1 scaling construction. The prerequisites are submitted
as separate units for independent review and publication before whole-task
completion.
