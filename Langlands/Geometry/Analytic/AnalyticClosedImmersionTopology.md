# Underlying topology of analytic closed immersions

A finite strong morphism between saturated presentations is proper on
the underlying spaces. The preimage of each original chart in the
saturated target is a recognized affinoid subset of the source.
Its spectrum is compact. For a closed subset of the source, its inverse
image on that spectrum is still compact. Mapping this compact set to
the target chart gives the intersection of the image with that chart.
The target chart is Hausdorff, so this intersection is closed in the
chart. The chart quasinet detects closedness in the ambient target.
The fibre over a point is also compact by restricting to a chart
containing it and taking the inverse image of the singleton in that
Hausdorff chart.

A closed strong immersion is finite and injective on points. Its
underlying continuous map is consequently a closed embedding. An
isomorphism of localized arrows induces homeomorphisms at both ends,
so the same result holds for the localized `closedImmersion` property.
The definition `closedImmersion.rangeHomeomorph` gives the homeomorphism
onto the image with its subspace topology.

These are internal consequences of the Library's finite recognition,
quasinet topology and analytic closed immersion monicity arguments.
