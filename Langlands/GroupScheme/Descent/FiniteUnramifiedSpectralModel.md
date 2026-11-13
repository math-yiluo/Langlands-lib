# Finite smooth group models over the actual spectral integer rings

This internal construction transports the previously constructed finite
coefficient model along `integerCoefficientsEquiv`. It retains the actual
integer inclusions and the recovery isomorphism over the maximal unramified
integers.

`baseIntegerIso` compares the spectrum of the given valuation integers with
the spectrum of `baseIntegers F`, using `localNormedField_integer`.
`coefficientIntegerIso` compares the spectrum of `extensionIntegers F E`
with that of the coefficient subring `integerCoefficients F E`, when
`E` is contained in the inertia fixed field.

`spectralIntegerInclusion` maps each spectral integer of `E` to the same
separable-closure element in `fixedFieldIntegers F`.
`spectralIntegerMap` is its contravariant spectrum map.
The two composition lemmas identify its composites with the coefficient
comparison and with the finite-stage integer map. In particular the latter
composite is the actual maximal-unramified integer map followed by the base
integer comparison.

`SpectralGroupModel` records a finite Galois arithmetically unramified
intermediate field, a smooth affine group over its actual spectral integer
ring, and the recovery isomorphism after the specified actual inclusion
into the maximal-unramified integers.
`GroupModel.toSpectral` pulls the coefficient group back along
`coefficientIntegerIso`; smoothness and affineness are preserved by base
change, and `pullbackComparison` gives the exact recovery isomorphism.
`spectralGroupModel` chooses this construction for a supplied smooth affine
group over the maximal-unramified integers.

The construction does not descend a supplied generic-fibre identification,
construct semilinear isomorphisms, or assert effectivity of descent data.
