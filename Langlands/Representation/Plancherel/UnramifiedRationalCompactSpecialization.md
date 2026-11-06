# Compact specialization of the actual rational normalized induced family

This internal adapter applies the generic compact specialization construction to
the actual rational normalized induced representation and its function-value
evaluation. The field and inducing-carrier universes remain independent, and the
regular algebra uses the complete rational norm-character family. The supplied
semidirect decomposition and closed unipotent image are retained.

The structural instances are those of the actual induced action with its
complex scalars restricted along constants. Its complex and regular scalar
actions commute because the regular algebra is commutative. On complex scalars,
the regular algebra acts by evaluation at the chosen unramified character.
`inducedGenericScalarExtension_eq` identifies the generic extension with the
existing `inducedScalarExtension`: their values on a pure tensor are the same
scalar multiple of the same actual function-value evaluation, and additivity
extends the equality to all tensors.

`inducedFixedScalarExtension` is that evaluation restricted to the literal fixed
vectors and then extended by scalars. For a compact open subgroup,
`inducedFixedScalarExtensionEquiv` applies the generic compact averaging argument
to this actual map. It requires the genuine
`InducedSpecializationBijective` hypothesis on the existing full induced
specialization; it does not prove or replace that hypothesis.

`inducedCompressedAction_stablePower` transfers stability of the universal
compressed operator raised to the supplied exponent to the specialized
normalized induction with exactly the same exponent. The generic construction
uses coefficient linearity, the fixed-vector equivalence and preservation of the
two square stability equalities under scalar extension. No flatness or
finite-generation assumption is added by this transfer.

This is a derived application of the actual evaluation adapter and the generic
compact specialization bridge. It constructs no exponent, asserts no family
finiteness and does not yet prove uniform stabilization over representations.
