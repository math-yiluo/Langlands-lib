# Restriction of the central defect along an extension of base

Take a central isogeny over `F` and a natural cocycle on the cover by
a normal extension `L/F`, with central lift data over `L`. Let `M`
contain `L` and another field `K` compatibly with `F`. The group of
`K`-automorphisms of `M` acts on the coefficient points over `M`
through its restriction of scalars to `F`. Its automorphisms restrict
to `L` by normality.

`IsCentralIsogeny.restrictGaloisLift` transports both the lifted values
and their kernel defect by restriction of automorphisms and extension
of coefficients. The multiplication identity for the new defect
follows because coefficient extension commutes with the kernel
inclusion, the isogeny and the compatible Galois actions.

Suppose a point of the source over `M` has image whose coboundary is
the restricted original cocycle. The coboundary of this source point
is a crossed lift of the restricted values. The central exactness
calculation then gives a primitive of the restricted defect, in the
actual kernel points over `M`. This is an internal comparison that
applies, in particular, when `K` is a completion and the cochain
has been lifted over a coefficient extension of `K`.
