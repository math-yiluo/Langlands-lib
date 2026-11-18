# Reduction of multiplicative extension splitting to connected-action rigidity

`IsSimplyConnected.multiplicativeExtensionSection` constructs a homomorphic
section of a flat homomorphism `q : H ⟶ G` with multiplicative-type full
kernel, for a simply connected semisimple target and an arbitrary affine
finite-type source over any field. The construction explicitly takes
`MultiplicativeTypeConnectedActionStatement` as an additional input.
It does not prove that rigidity proposition.

The source is first replaced by its full identity component using
`FiniteTypeIdentityComponent.groupScheme`. This retains its possible
nilpotents, is connected and affine of finite type, and has an inclusion
that is both open and closed. Openness preserves flatness of the
restricted quotient. Closedness preserves multiplicative type of its
actual full kernel.

That kernel is normal on every test scheme, as follows by applying the
restricted homomorphism to conjugates. The supplied connected-action
rigidity proposition therefore makes it central in the connected source.
`IsSimplyConnected.exists_section_of_central_multiplicative` supplies a
section into this component. Composing with its inclusion gives a
section into the original source.
`multiplicativeExtensionSection_comp` proves the section identity.

`simplyConnectedMultiplicativeExtensionSplit_of_connectedAction` packages
the construction as an implication from the published
`MultiplicativeTypeConnectedActionStatement` to the exact unchanged
`SimplyConnectedMultiplicativeExtensionSplitStatement`, in every universe.
The target's surjectivity hypothesis is unnecessary for this construction;
the argument uses its flatness hypothesis.

## Provenance

This is an internal derived construction and reduction theorem. It
combines the full finite-type identity component, closed-subgroup stability
for multiplicative-type full kernels, the supplied connected-action
rigidity proposition, and the central multiplicative-type section
construction. An unconditional exact-target proof must supply an accepted,
published proof of connected-action rigidity.
