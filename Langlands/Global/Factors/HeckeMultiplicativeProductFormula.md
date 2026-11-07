# Actual multiplicative product formulas for Hecke characters

This internal derived module applies the proved full-tail multiplicative kernel
lemma to the original Hecke character on the product of integral local units.
The chosen finite set `multiplicativeIntegralControl` controls that restriction.
`nonunitPlaces` records the places where the value or inverse of the actual
idele is nonintegral; outside this finite set, `integralUnitAt` packages its
actual coordinate and inverse as an integral unit.

The finite partial product inserts the selected actual local coordinates. The
idele decomposes into its infinite part, this partial product and an integral
remainder that is one on the controlled places. The remainder has character
value one, even if it has infinitely many nontrivial coordinates.

Finite reconstruction at the infinite places gives the product of the actual
archimedean Hecke components. Combining these identities gives the full local
product formula. On principal ideles the original character has value one, so
the same product equals one. All assertions retain the actual completion
projections and original Hecke components on a number field in any universe.

The provenance is direct continuity and coordinatewise multiplication in
Mathlib's adelic model. These identities do not prove the global functional
equation or any continuation assertion.
