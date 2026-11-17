# Integral-isomorphism transport of actual local quasi-isogenies

This internal construction concerns globally coordinated formal O-modules
over a commutative O-algebra R, with an O-algebra field F. R and F share a
universe, and the four finite coordinate types may differ. It uses the actual
rational Hom sheaves and the existing pointwise local scalar-isogeny condition.

For integral isomorphisms a from M to M' and b from N to N', the constructed
section map sends z to b composed with z composed with the inverse of a.
The integral maps enter as their actual rational sheaf sections on the open.
Bilinearity gives an F-linear map, and the section category laws show that
transport by the inverse isomorphisms is its inverse. These maps therefore
give an actual linear equivalence and commute with restriction.

An integral isogeny f is transported to b composed with f composed with the
inverse of a. The existing isomorphism-of-arrows theorem transports both its
represented finite locally free kernel and its affine fppf lifting property.
No general composition theorem for finite kernels is used.

For a local scalar-isogeny section, retain the original neighbourhood and
exponent at each point. Extend a and b to its actual structure algebra and
transport the integral numerator by those isomorphisms. The preceding kernel
transport proves that this numerator is an isogeny. Restriction naturality,
bilinearity and agreement on integral images prove its required scaled
section equality. Thus transport preserves the local condition. Applying
inverse transport proves reflection as well.

`LocalQuasiIsogeny.idOn` constructs the identity on every open, using the
actual identity section and an exponent-zero witness. The new transport
operation carries the nonzero scalar hypothesis unchanged and transports the
actual global scalar-divisibility hypotheses by the existing integral
isomorphisms. Equality on the rational section proves its restriction and
inverse laws. `LocalQuasiIsogeny.transportIsoEquiv` packages this as a genuine
equivalence of the existing local quasi-isogeny types.

All provenance is internal: these are derived operations on previously
defined objects and proved section laws. Arbitrary composition or inversion
of local quasi-isogenies, nilpotent rigidity, rational heights and
representability remain separate obligations.
