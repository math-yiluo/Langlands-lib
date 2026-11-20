# Recognized closed immersions from affinoid quotient tests

Suppose the pullback of a localized analytic morphism along every
small affinoid spectrum is represented by the spectrum of a presented
closed quotient. `closedImmersion_of_affinoidQuotientPullbacks`
derives the Library's closed immersion property.

First choose a strong representative after an isomorphism of the
source. For each recognized affinoid subset of the target, use the
small spectrum of its algebra as the test. The quotient pullback and
the analytic domain pullback identify the inverse-image domain with
the small spectrum of the quotient. The isomorphism from the
inverse-image domain to that spectrum has a strong representative
because the spectrum has a greatest chart. This representative is
a quasi-isomorphism, so the recognized whole chart of the spectrum
transports to a recognized affinoid subset of the domain. The domain
inclusion transports it into the source's saturated atlas.

The source recognized subset lies over the given target subset, so
the recognized strong map has their full bounded pullback. The
small spectra of this pair of charts give a second pullback square.
Its isomorphism with the quotient square identifies the full
bounded map with the closed quotient followed by a bounded algebra
equivalence. Admissibility therefore follows from the actual
quotient map. The source and target saturation comparisons and the
chosen localized representative give the required arrow isomorphism.

This is an internal criterion for the Library's definition of closed
immersion. The proof uses the universal property of domain inclusions,
recognition under quasi-isomorphisms, and the equivalence between
localized affinoid morphisms and actual bounded algebra maps.
