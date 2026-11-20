# Rational sections on a formal idempotent image

Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996), (6.17) and Lemma 6.44, printed pp. 309–310 (PDF pp. 321–322), use the summands of a split polarized group and the induced quasi-isogenies. This module gives the restriction calculation at the level of the rational Hom sheaf.

`Hom.IdempotentImage.restrictSection` composes a section with the integral source inclusion and the integral target projection. For an integral map this is the rational section of the corresponding integral restriction. For a section commuting with the projectors, inclusion after restriction recovers the section after source inclusion. This identity gives composition, and the retraction equation gives the identity section.

An invertible section commuting with projectors has an inverse commuting with them in reverse. `Hom.IdempotentImage.restrictSectionIso` therefore restricts both directions and verifies the inverse equations on the image laws. The restriction formula is compatible with shrinking the open and with coefficient pullback. The coordinate laws and retraction maps are the input data of `Hom.IdempotentImage`.
