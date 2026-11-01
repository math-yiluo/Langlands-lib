# Actual geometric section pullback and etale restriction

This internal comparison identifies the actual arbitrary-morphism section
pullback with the earlier restriction construction when the scheme morphism
is etale. It uses the existing small-etale sites and their actual
composition/base-change adjunction. No comparison equation is assumed.

The schemes and commutative coefficient ring use universe `u`, with
`ModuleCat.{u} R`-valued sheaves. There is no finiteness, field, Noetherian,
local-constancy, or derived-localization hypothesis.

The existing isomorphism `inverseImageIsoRestriction` is the unique
comparison of the two left adjoints to the actual geometric direct image.
`inverseImageIsoRestriction_unit` records its unit compatibility.
`inverseImage_etale_preservesInjectives` transports the proved injective
preservation of etale restriction along that coefficient isomorphism.
This assertion requires an etale base map.
`inverseImageInjectives` constructs the resulting actual functor between
the full subcategories of injective module sheaves; its object property
uses the preceding proof, and its additivity follows from the geometric
inverse-image functor.

`restrictionGeometricUnit_terminalSections` proves that the restriction
adjunction unit followed by the direct-image terminal-section comparison
is the earlier terminal-section map. Both sides are images under the
original sheaf of maps into the terminal small-etale object, so terminal
uniqueness proves equality. `restrictionGeometricUnit_sections` transports
this equation through the existing global-section identifications.

`sectionsPullback_restriction` then proves that arbitrary-morphism section
pullback followed by sections of the actual inverse-image/restriction
isomorphism equals `EtalePullback.sectionsMap`. The proof uses naturality of
the direct-image section comparison, functoriality, unit compatibility,
and the preceding unit formula. `sectionsPullback_restriction_eq` gives
the same equality of natural transformations.

The provenance is internal categorical infrastructure from the existing
`EtaleInverseImageRestriction`, `EtaleDerivedGlobalNormalization`, and
Mathlib's uniqueness-of-adjoints, injective-isomorphism transport, and
terminal-object constructions. Derived and higher-cohomology comparison,
compact supports, coefficient change, smooth actions, and Harris
specialization remain separate obligations.
