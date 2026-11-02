# Local finite presentation of actual line bundles

This internal result connects the Library's actual locally free rank-one
sheaves to Mathlib's `SheafOfModules.IsFinitePresentation`. It applies to
arbitrary schemes in every universe, without a noetherian assumption.

`IsLocallyFreeRankOne.finitePresentationData` chooses one trivializing
neighborhood for each point. These opens cover the scheme. On each open, the
published `Langlands.Scheme.Modules.unitLocalBasis` identifies the over-site
restriction with the free sheaf on `PUnit`. Transporting its standard generating
sections gives an isomorphism from this free sheaf to the restriction.
Mathlib's `LocalGeneratorsData.quasiCoherentData` then supplies a presentation
with those one-element generators and empty relations. Both indexing types are
finite. The definition returns these actual quasicoherent presentation data
together with their finite-presentation certificate.

`IsLocallyFreeRankOne.isFinitePresentation` derives the sheaf's local
finite-presentation property from these data.

`LineBundle.isFinitePresentation` gives the corresponding instance for the
underlying module sheaf of an actual line bundle.
`IsLocallyFreeRankOne.isFinitePresentation_pullback` applies the same theorem
after the published preservation of local rank one by ordinary scheme-module
pullback.

The construction is derived from the existing local trivializations and
Mathlib's free-sheaf presentations. It proves no atlas existence or
representability assertion.
