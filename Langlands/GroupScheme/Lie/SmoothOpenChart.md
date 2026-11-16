# Smoothness from a nonempty smooth open chart

`HasNonemptySmoothOpenChart H` is the proposition that there exist a scheme
over the field and an open immersion from it into `H`, with smooth
structural morphism and nonempty underlying space.

This internal lemma extends the existing smooth-open-subgroup argument to
an arbitrary nonempty smooth scheme included openly in a locally
finite-type group scheme over a field. The chart requires no group
structure and need not contain the identity.

After extension to an algebraic closure, surjectivity of the field
extension preserves nonemptiness of the chart. The open immersion
identifies its smooth locus with the inverse image of the group's smooth
locus, so the latter is nonempty. The existing
`smooth_of_nonempty_smoothLocus` propagates smoothness by translations.
Finally, fpqc reflection along the field extension gives smoothness over
the original field. This is a derived geometric lemma using the published
translation and descent interfaces.
The theorem `HasNonemptySmoothOpenChart.smooth` applies the same result to
the existential chart condition.
