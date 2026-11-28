# Clopen affinoid domains in the localized category

A clopen subset of the small spectrum of a presented affinoid algebra
pulls back to a clopen subset of its bounded spectrum. The idempotent
of that subset defines a rational chart. Gluing a section with zero
on the complementary chart gives norm-controlled preimages of the
chart restriction. The restriction is finite Banach and surjective.
Flatness of the idempotent localization then gives algebraic finite
étaleness. The chart spectrum embeds into the original spectrum, so
it is small in the same space universe.

The ring restriction is an epimorphism. Its pushout along itself
therefore has identity legs, giving the identity kernel pair for
the localized spectrum map. The spectrum map is étale by the
finite affinoid étale criterion. Its range is the given clopen set.
`clopenDomainIso` identifies the chart spectrum with the open
analytic domain of that set, and its composite with the domain
inclusion is the spectrum map of the actual chart restriction.

The field is complete and ultrametric, with independent field and
space universes. For an étale monomorphism with a specified clopen
range in a small affinoid spectrum, `etaleMonoClopenImageIso` first
identifies the source with its open image, then uses the inverse of
`clopenDomainIso`. The resulting isomorphism commutes with the
morphisms to the original affinoid spectrum.
