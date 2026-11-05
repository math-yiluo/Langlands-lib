# Hopf maps of actual affine groups over arbitrary rings

`AffineHopfMorphism.pullback` takes an actual homomorphism between affine group
schemes over `Spec R` to the contravariant morphism of their actual coordinate
Hopf algebras. Here `R` is an arbitrary commutative ring. The construction uses
the fully faithful Hopf spectrum functor and the published affine-coordinate
isomorphisms, so its spectrum recovers the supplied homomorphism exactly under
those isomorphisms.

The accompanying criterion equates closed immersion of that actual morphism
with surjectivity of its Hopf map. In one direction, the global-sections map
of a closed immersion of affine schemes is surjective, and the canonical
`Γ(Spec A)` comparisons recover the original ring map. In the other, the
spectrum of a surjective ring map is a closed immersion. Transport through
the two coordinate isomorphisms proves the actual group-scheme assertion.

This is an internal interface derived from the existing affine Hopf spectrum
equivalence and Mathlib's affine closed-immersion criteria. It generalizes the
field-base pattern used by `AffineCoordinates.hopfRestriction` without changing
that existing interface.

The affine-spectrum surjectivity step reuses
`CentralExtensionHopfSpec.surjective_of_isClosedImmersion`.
