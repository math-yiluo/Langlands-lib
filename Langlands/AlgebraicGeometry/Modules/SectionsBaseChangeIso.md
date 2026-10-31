# Canonical sections base change along isomorphisms

This internal consequence of the published sections constructions works in
an arbitrary universe `u`. For schemes `X`, `Y`, rings `R`, `S`, and a
commuting square `g ≫ f = f' ≫ Spec.map φ`, it proves invertibility
of the specified canonical sections maps when the relevant maps are
isomorphisms. No quasi-coherence or flatness assumption is required.

`isIso_sectionsBaseChangeMap_of_isIso` assumes only that `g` is an
isomorphism. The published `pushforwardEquivalence (asIso g)` makes
pushforward an equivalence, so the pullback–pushforward adjunction unit
is invertible. The actual ordinary sections map is relative sections of
that unit followed by the composition and base-ring isomorphisms.
Thus every factor is invertible, including when the base-ring map is
not an isomorphism. `sectionsBaseChangeIso` packages this exact map as
an isomorphism.

`isIso_scalarSectionsBaseChangeMap_of_isIso_sections` assumes that `φ`
is an isomorphism and that the ordinary sections map is invertible.
The ring isomorphism associated to `asIso φ` supplies Mathlib's
restriction-of-scalars equivalence. Its fully faithful right adjoint
makes the scalar adjunction counit invertible. The formula for the
inverse hom-set equivalence expresses the actual scalar map as scalar
extension of the ordinary map followed by this counit, proving the
claim.

`isIso_scalarSectionsBaseChangeMap_of_isIso` applies both results when
`g` and `φ` are isomorphisms. `scalarSectionsBaseChangeIso` packages
the actual scalar map. These constructions allow affine presentations
to be changed without replacing the canonical maps by unspecified
isomorphisms.

The provenance is entirely internal: the proof uses
`pushforwardEquivalence` from `SchemeIsoCohomology`, the actual definitions in
`CohomologyBaseChangeZero`, the isomorphism of rings associated with a
categorical ring isomorphism, and the standard fully faithful
adjunction and scalar restriction equivalence APIs in Mathlib. It
proves neither general Cartesian affine base change nor the relative
cube theorem.
