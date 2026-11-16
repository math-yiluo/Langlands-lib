# Transport of étaleness of open-domain inclusions

This is an internal, derived transport argument for
`Langlands.Analytic.SaturatedAtlasPresentation.EtaleOpenDomainStatement`.
It uses the existing analytic-domain factorization and the published localization
constructions; no additional geometric assumption is supplied.

The existing `domainRestrictIso` from `QuasiEtaleDomains`, specialized to
the two equal atlas universes used here, restricts an ambient isomorphism to two analytic domains
whose carriers map into each other under its forward and inverse maps.
Its inverse identities follow from the domain factorization identities and
cancellation of the canonical domain monomorphisms. Thus it identifies actual
analytic morphisms, retaining their bounded pullback data, rather than inferring
equality of morphisms from equality of point maps.

`domainInclusionArrowIso` packages this restriction and the ambient
isomorphism as an isomorphism between the two canonical inclusion arrows.
`etaleOpenDomainStatement_of_iso` uses the preimage of an open subset under
the inverse ambient isomorphism, and transports étaleness through that arrow
isomorphism using the existing `etale.RespectsIso` instance.

`etaleOpenDomainStatement_of_fullRecognition` reduces the result for arbitrary
analytic spaces to the result for all full-recognition presentations. For the
presentation underlying the analytic space, it composes the inverse of the
localized `saturationIso` with the localized quasi-isomorphism
`localDomainToFullRecognitionHom`. It then applies the preceding transport
theorem. The étaleness assertion on full-recognition presentations is an
explicit premise of this reduction and is proved separately in the proof module.
