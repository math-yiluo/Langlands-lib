# Base change of the reductive identity-component locus

This is a derived comparison unit for the actual locus defined in
`Langlands.GroupScheme.Reductive.IdentityComponentLocus`. It retains arbitrary
schemes, arbitrary base-change morphisms, and smooth affine group schemes
whose fibres may be disconnected. It proves no openness assertion.

First, reductivity of the identity component is invariant under any field
extension. The implemented proof uses `IdentityComponent.baseChangeIso`
to compare the actual identity components, the preservation theorem
`connectedReductiveFieldExtensionStatement`, and reflection
`IsConnectedReductive.of_fieldExtension`. These are the existing geometric
connected-reductivity predicates, without a perfectness or algebraicity
restriction on the extension.

For an actual field-valued point, `fieldPointFiberIso` compares its pullback
with the actual residue-field fibre followed by scalar extension along
`fieldPointResidueMap`. Applying `IdentityComponent.mapIso` and
`IdentityComponent.baseChangeIso` constructs the actual group-scheme
isomorphism `fieldPointIdentityComponentIso`. Preservation and reflection
of connected reductivity across this comparison prove
`fieldIdentityComponentReductive_iff_residueFiber`. Applying this comparison
to the chosen geometric point proves
`mem_identityComponentReductiveLocus_iff_residueFiber`; the image of that
point is the original base point by `Scheme.fromSpecResidueField_apply`.
Consequently every specified field-valued point detects the exact geometric
locus at its image.

Finally, `baseChangeCompIso` compares a geometric fibre after arbitrary
base change with the single pullback along the composite field-valued
point. The preceding comparison identifies its condition with membership
at the image in the original base. Extensionality gives the exact set
equality in `identityComponentReductiveLocus_baseChange`. No relative
identity-component model or chosen compatibility between algebraic
closures of distinct residue fields is assumed.

The provenance is internal: these are consequences of the published
identity-component, field-extension, and actual-fibre comparison results.
They supply the change-of-base comparisons needed for a local proof of
Conrad's Proposition 3.1.9(1); the relative structural proof of that
openness theorem remains separate.
