# Sections of central multiplicative-type extensions over arbitrary fields

`IsSimplyConnected.centralMultiplicativeSection` constructs a homomorphic
section of a flat homomorphism `q : H ⟶ G`, where `G` is simply connected
semisimple, `H` is affine and locally of finite type over an arbitrary
field, and the full kernel of `q` is central and of multiplicative type.
`centralMultiplicativeSection_comp` proves the section identity. No
smoothness or connectedness of `H` is assumed.

The existence theorem passes to an algebraic closure of the field. Simple
connectedness of the target and multiplicative type of the full kernel
persist under that extension, with the actual base-change kernel
isomorphism supplying the latter comparison. Over this perfect field,
the source's reduced identity core is smooth connected reductive by
`IsConnectedReductive.identityCore_of_multiplicativeTypeKernel`.
`ReducedSubgroup.identityCore_comp_flat_surjective` makes its composite
with the quotient faithfully flat and in particular surjective.

The core inclusion is a closed immersion, hence monic. It therefore
provides the geometric reductive lift required by
`IsSimplyConnected.exists_section_of_geometric_reductive_lift`.
That construction uses the derived subgroup to split over the algebraic
closure and checks uniqueness on the whole fpqc overlap to descend the
section to the original field.

## Provenance

This is an internal derived construction combining
`SimplyConnected.GeometricCentralSection`,
`Reductive.MultiplicativeKernelReduction`, simple connectedness under
field extension, and multiplicative type under algebraic field extension.
The centrality of the full original kernel is an explicit hypothesis.
Removing that hypothesis requires passing to the original source's
identity component and applying multiplicative-type rigidity; this
module does not assert that reduction.
