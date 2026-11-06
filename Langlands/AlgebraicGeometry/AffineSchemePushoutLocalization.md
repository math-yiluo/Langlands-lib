# Localized pullback square

Internal helper for affine scheme pushouts. The theorem proves that the square
formed by compatible localizations of a canonical ring pullback is again a
categorical pullback of commutative rings. The induced map from the localized
pullback to the pullback of localizations commutes with the algebra maps.
The localization helper identifies both rings as localizations at the same
element, so this induced map is bijective. Transport of the canonical pullback
cone along the resulting ring isomorphism proves the claim.

`localizationPullbackConeIsLimit` supplies the resulting limit structure on
the cone with the displayed localized projection homomorphisms. It is
constructed from the proved pullback property. No surjectivity premise is
needed for this localization step.
