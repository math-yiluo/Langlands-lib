# Scalar Čech maps and base change of perfect models

This internal construction compares the already specified scalar Čech map with
the already specified base change of a perfect model. All schemes, rings and
modules lie in an arbitrary common universe. The base-ring homomorphism is
arbitrary.

`scalarCechDerivedBaseChangeMap` applies the localization functor to the actual
scalar-linear alternating Čech cochain map after extension from natural to
integer degrees. The source transport is the specified isomorphism commuting
extension of scalars with extension of the complex by zero.

`cechDerivedBaseChangeMap_eq_adjunct` identifies the semilinear derived Čech map
with the canonical derived adjunction unit followed by restriction of scalars
of this scalar-linear map. No perfectness of the Čech complex is assumed.
The proof checks compatibility of the chain adjunction and extension by zero
degreewise. In degrees in the image the assertion is the ordinary scalar
adjunction formula; in the other degrees the source is zero. Naturality of the
exact scalar-restriction localization comparison then gives the derived
identity.

For a Cartesian square over spectra, a line bundle `L`, an ordered affine cover
and a chain map `v` from an integer-indexed complex into the integer extension
of its alternating Čech complex, `cechBaseChangeCochainMap` first extends `v`
by scalars and then applies the actual scalar Čech map. The morphism to the
original scheme is affine because it is the pullback of a morphism between
affine schemes.

`perfectModelBaseChange_cechDerivedComparison` says that if the source complex
is strictly perfect, applying `perfectModelBaseChange` to `Q(v)` followed by the
named canonical Čech comparison equals `Q` of this explicit chain map followed
by the target canonical Čech comparison. It applies the injective perfect-source
scalar Hom equivalence, uses naturality of the derived unit for the arbitrary
Čech target, and then uses the preceding adjunct identity and
`cechDerivedComparison_baseChange`. The higher-direct-image condition in that
last theorem is supplied by the existing vanishing theorem for the pullback of
a line bundle along this affine morphism.

This is an equality of the actual derived morphisms. It asserts neither that
the given chain map is a quasi-isomorphism nor that its scalar extension or the
base change of the perfect model is invertible. Separatedness and flatness
are not needed for the equality. The provenance is internal: all maps and
comparisons come from the imported definitions, naturality and adjunction;
no external geometric theorem is restated here.
