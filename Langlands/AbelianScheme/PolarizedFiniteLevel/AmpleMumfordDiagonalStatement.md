# Ampleness of the diagonal bundle of an actual ample Mumford map

`AmpleMumfordDiagonalStatement` says that over a one-point base scheme,
the diagonal Poincaré bundle attached to a map with an actual ample
Mumford presentation is ample. It uses the existing prerequisite package,
abelian scheme, dual witness, Poincaré family, and diagonal-bundle construction.
A field spectrum is a special case of the one-point base assumption.

This is an internal consequence of the normalized Mumford-family formula,
Poincaré multiplicativity in the abelian-scheme variable, and the published
ampleness results for tensor products and pullbacks along closed immersions.
For an ample presentation bundle `L`, evaluation of the Mumford family at
`(id, [-1])` gives the class `[L]⁻¹ · [([-1])*L]⁻¹`: the product point is
the unit section, whose bundle class is trivial over a one-point base.
Poincaré multiplicativity makes this class the inverse of its value at
`(id,id)`. Thus the diagonal bundle is isomorphic to `L tensor ([-1])*L`.
Inversion is an isomorphism, so both factors are ample, and their tensor
product is ample.

This focused statement assumes an ample presentation on the specified base.
It does not descend ampleness along a field extension, derive a presentation
on the original field from `HasFieldAmpleMumfordPresentation`, or assert
cohomology vanishing or a degree formula. The unconditional cubic-fibre
cohomology proposition remains required.
