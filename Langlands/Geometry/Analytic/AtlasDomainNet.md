# The net of all actual local full affinoid domains

This module constructs the enlarged net in Berkovich, *Etale cohomology for
non-Archimedean analytic spaces* (1993), Proposition 1.2.6, printed p.17
(PDF p.14). The enlarged family consists exactly of subsets that are full
affinoid domains in one original chart. Its elements are the ambient loci of
the already constructed actual `LocalDomain` presentations. No directedness,
greatest chart or ambient Hausdorffness assumption is added.

Original-chart localization preserves the exact ambient image by the existing
extension image identity and localization round trip.
`partInChart` intersects a local domain with a contained original relative
chart domain and localizes that actual intersection using its original
second bounded quotient projection. Its ambient image is exactly the original
local-domain locus intersected with that original chart domain.
`interInChart` intersects the two resulting actual full domains over a common
original chart. Injectivity of that chart and the preceding image identities
give exactly the intersection of both original loci with the common chart.

`localDomainFamily` is the family of all actual local-domain loci. Each original
chart belongs to it using the actual whole-spectrum domain, so the original
quasinet proves that the enlarged family is a quasinet.

For two local domains and a point in their intersection, the original net gives
a finite relative neighborhood family of common original charts, all containing
the point and contained in both containing original chart domains. Replace each
such chart with the actual `interInChart` just constructed. Its locus lies in
the original local-domain intersection and contains the point. The union of
these new members contains the intersection of that local-domain intersection
with the original finite chart union. Monotonicity of relative neighborhoods
and the relative self-neighborhood property make this a neighborhood within
the intersection. This proves the displayed `LocallyRefines` result and hence
the restricted-family quasinet for every pair of enlarged members.
`isNet_localDomainFamily` combines this with the enlarged quasinet.

Every member is compact and Hausdorff with its actual subspace topology,
by the existing actual-spectrum homeomorphism for `LocalDomain`. The ambient
space itself may fail to be Hausdorff, and the proof does not assume that the
entire intersection of two local domains is compact or a single affinoid
domain.

The implemented proof follows the finite relative-neighborhood construction
in the first paragraph of the proof of Proposition 1.2.6. It uses the existing
full affinoid-domain meaning, actual quotient intersections and original-chart
localization; these retain arbitrary positive radii, trivial valuations,
nonreduced or zero quotients and permitted empty families. The module proves
the enlarged net and compact-family property. Choosing affinoid presentations
and constructing the extended atlas with this net, strong morphism extension,
analytic or equivariant sites and the Harris tower remain further work.
