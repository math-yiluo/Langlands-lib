# Finite primitive generators in corepresented coordinates

This internal adapter exposes the primitive generators of a smooth commutative
prime-exponent affine group in the `Corepresented.primitiveFunctions` interface.
The base is any field of characteristic `p`, where `p` is prime, and the universe
is arbitrary. The group may be disconnected and the field may be finite or
imperfect. The exponent assumption remains `HasUniformPowerExponent G p`, on
all relative scheme tests.

The coordinate Hopf algebra and `AffineCoordinates.algebra G` have the same
underlying algebra. The theorem `isPrimitiveFunction_of_isPrimitiveElem` shows
that a primitive element of that Hopf algebra is additive on every algebra-valued
point of `AffineCoordinates.functor G`. Its proof uses
`HopfPrimitive.mul_unop_hom_apply`: under `corepresentation G`, the coordinate
map is the underlying algebra map of a point of the coordinate cogroup. Thus
canonical Hopf primitivity gives the required pointwise addition identity.
`mem_primitiveFunctions_of_isPrimitiveElem` then applies the existing
`Corepresented.mem_primitiveFunctions_iff` to put this same element in the
primitive-function submodule. This comparison needs only affineness over the
field; it does not require smoothness or the exponent assumption.

For a smooth commutative group killed by `p`,
`exists_finite_corepresented_primitive_generators_of_smooth_uniformExponent`
uses `exists_finite_primitive_generators_of_smooth_uniformExponent` from
`SmoothPTorsionPrimitiveGenerators`. It maps that finite set of canonical Hopf
primitives into the primitive-function submodule, leaving each underlying
algebra element unchanged. Equality of the two sets of underlying elements
preserves the assertion that their algebraic adjoin is the whole coordinate
algebra. In particular, this is a finite set of algebra generators contained in
the primitive submodule; it makes no finite-dimensionality assertion about the
entire primitive submodule.

`finiteCorepresentedPrimitiveGeneratorsOfSmoothUniformExponent` uses classical
choice to return a finite set in the primitive-function submodule together with
its algebra-generation proof. This is the data interface for consumers that
need generators in the corepresented presentation of the original affine group.

The provenance is internal: the module combines the existing Hopf primitive
point formula, the existing characterization of primitive functions, and the
original-field finite primitive-generation theorem. It adds no separate
classification, scalar-descent, or Frobenius-module construction.
