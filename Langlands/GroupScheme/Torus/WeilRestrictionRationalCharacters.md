# Rational evaluation of embedding characters of Weil restriction

This internal helper connects the published scheme-point embedding coordinates
of the Weil restriction to the published rational tensor-unit coordinates.
It assumes a finite field extension and bijectivity of tensor evaluation in
the coefficient field; finite separability and splitting of minimal polynomials
supply this assumption through `embeddingEvaluationStatement`.

`extendedUnitPoint` is the multiplicative map from `Kˣ` to rational points
of the base-changed Weil restriction. It first converts a unit to the
ground-field rational point using the inverse of `rationalUnitsEquiv`, then
extends the point to the coefficient field. This construction needs no
splitting hypothesis; that hypothesis is used in the character formulas.

`pointsEquiv_rationalBaseChange` identifies the two global tensor-unit
coordinates by naturality along the morphism with underlying identity.
`tensorCoordinate_affineSections` checks tensor evaluation against the
spectrum/global-section isomorphism on pure tensors and extends additively.
`embeddingPointsEquiv_rational` transports the global-section embedding
coordinate through the spectrum/global-section isomorphism and identifies it
with tensor evaluation of `extensionUnitsEquiv`.
`embeddingPointsEquiv_rationalExtend` specializes this to an extended rational
point: the coordinate at an embedding is the image of its `rationalUnitsEquiv`
unit under that embedding.
`rationalCharacterEval_extend_eq_prod` therefore identifies every actual
character value with the monomial whose exponents are the published embedding
character coordinates.
`rationalCharacterEval_extendedUnitPoint_eq_prod` gives the same identity
directly for the `extendedUnitPoint` construction and a prescribed unit.

The proofs use the published affine/global-section comparison and naturality
of the Weil-restriction tensor-unit coordinates. The monomial identity follows
from `embeddingCharacterEquiv_symm_points` by applying the unit map of
`Scheme.ΓSpecIso` and its preservation of products and integer powers.
These are derived identities between the existing constructions, with no new
literature claim.
