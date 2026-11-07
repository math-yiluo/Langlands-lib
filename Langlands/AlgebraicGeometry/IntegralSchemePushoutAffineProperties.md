# Morphism properties of the canonical affine pinching cocone

This internal construction takes commutative rings `R`, `S`, `T` in an arbitrary
common universe, a surjective map `f : R → T`, and an integral map `g : S → T`.
The vertex of the cocone is the spectrum of the actual compatible-pair ring
`f.pullback g`. Its arrows are the spectra of the two ring projections.

`isIntegralHom_specMap_pullbackFst` applies the intrinsic ring projection theorem
from `IntegralPullbackProjection` and Mathlib’s equivalence between integrality
of a ring map and integrality of its spectrum map. The proof of that imported
ring theorem lifts a monic polynomial and corrects its constant term.

`isClosedImmersion_specMap_pullbackSnd` uses surjectivity of the second projection,
which follows from surjectivity of `f`, and the spectrum closed-immersion theorem.
No integrality assumption on `g` is needed for this second property.

`integralAffinePushoutCocone` bundles the actual scheme cocone and the two proved
morphism properties. Commutativity is the defining equation of compatible pairs,
transported by the spectrum functor. This unit does not assert the cocone’s
pushout universal property, a cartesian property, or any global gluing result.
The derivation uses the named internal ring construction and Mathlib directly;
no additional external mathematical result is assumed. Zero rings are allowed.
