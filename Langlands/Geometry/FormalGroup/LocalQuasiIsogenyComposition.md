# Composition of local quasi-isogenies from finite-kernel composition

The construction applies to formal `O`-module laws with finite coordinate
types over a commutative `O`-algebra `R`, and an `O`-algebra field in the
universe of `R`. Its additional premise is the Library's
`Hom.FiniteKernelCompositionStatement` for the three formal laws over
each open's actual structure-section algebra.

At a point of the given open, the proof intersects the two opens on
which scalar powers of the sections have integral isogeny numerators.
The existing restriction maps take the two actual numerators to isogenies
on the intersection. The finite-kernel composition premise and the
existing fppf local lifting composition law make their composite an
isogeny. The exponent for the composite is the sum of the two exponents.
Bilinearity of section composition identifies the scaled composite
section with the image of the composite numerator.

`LocalQuasiIsogeny.comp_of_finiteKernelComposition` retains the source
and target divisibility and the scalar nonvanishing. Its underlying
section is the actual composite. The section restriction law and
extensionality show that restriction commutes with this construction.

This is an internal reduction of local quasi-isogeny composition to the
named finite-kernel composition target on the open coefficient algebras.
