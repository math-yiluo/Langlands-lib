# Rational density for smooth schemes over separably closed fields

This internal derived construction proves that every nonempty smooth affine
scheme over a separably closed field has an actual rational section. It then
proves Zariski density of actual rational sections for every smooth scheme over
that field. The field and schemes have arbitrary common universe `u`. There is
no perfectness, characteristic, affineness, connectedness or nonemptiness
hypothesis in the final density theorem beyond the stated smooth structure map;
density is vacuous for the empty scheme. No algebraic rational-point statement
is assumed.

`infinite_of_isSepClosed` proves that the field is infinite. In the finite case
the field would be perfect, hence algebraically closed by separable closedness;
algebraically closed fields are infinite. The other case supplies infinitude
directly.

`hasDenseRationalPoints_finitePolynomialSpec` transports the existing
`hasDenseRationalPoints_polynomialSpec` through a polynomial-variable renaming
isomorphism. The `ULift` in this renaming reconciles the fixed universe of
`Fin n` with the field's arbitrary universe. It does not change the field.

`nonempty_rationalPoint_of_smooth_algebra` chooses a prime of the nonzero smooth
algebra and applies Mathlib's
`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`. This produces a
localization away from an element outside the prime, together with a standard
étale algebra structure over a finite polynomial ring. The localization has a
prime obtained by extending the original prime. The induced étale morphism has
nonempty open image in polynomial affine space. Rational density supplies an
actual rational point in that image, and
`Scheme.exists_fac_of_etale_of_isSepClosed` lifts the point to the localization.
The two scalar towers show that composition to the original affine scheme is
a section over the original field.

`nonempty_rationalPoint_of_smooth_spec_of_isSepClosed` applies the algebra result
to the ring homomorphism corresponding to an arbitrary smooth spectrum
morphism. `rationalPointOfSmoothSpecOverSepClosed` chooses its actual section.
`hasDenseRationalPoints_of_smooth_of_isSepClosed` then takes any nonempty open in
a smooth scheme, chooses a nonempty affine open neighborhood inside it, obtains
its rational section, and composes with the open immersion. The resulting
rational section meets the original open.

The proof uses the published polynomial density toolkit and Mathlib's local
smooth structure, openness of étale morphisms and separably closed étale-point
lifting. It does not invoke the separate conditional geometrically reduced
algebra rational-point theorem, and does not establish that more general theorem
or the central unipotent woundness criterion by itself.
