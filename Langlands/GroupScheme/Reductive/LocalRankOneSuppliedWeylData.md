# Etale cell normalization for supplied Weyl root maps

This internally derived module works over an arbitrary commutative local
ring. It assumes an affine reductive group, a closed fibrewise maximal
coordinate split torus, its fibrewise root datum, an isolating cocharacter,
and supplied opposite root parametrizations whose Weyl product acts by the
prescribed root reflection.

A monomorphic group inclusion reflects a specified normalizing action,
by the existing `IsNormalizingPoint.of_comp`. Applying this to the actual
relative cocharacter centralizer proves that
the lifted root maps retain the original reflection.

For any supplied affine etale unit-cell data in that centralizer, the
associated coefficient-ring `WeylData` has beta equal to one. The supplied
reflection survives coefficient extension in the standard torus
coordinates. The pulled-back centralizer is reductive and its coordinate
split torus is closed and fibrewise maximal, so it self-centralizes.
The rank-one uniqueness theorem then forces beta to equal one.
`suppliedAffineEtaleWeylData` packages these same affine etale Weyl data
together with that equality.

The etale data are supplied; the theorem does not require their projection
to be surjective. The full local Isomorphism Theorem remains a separate
obligation.
