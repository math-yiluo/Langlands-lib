# Geometric base change of atlas cover incidence

This internal construction proves the base-change compatibility needed to turn
closed atlas overlap images into the actual geometric incidence predicates in
the component-count problem. It combines the earlier atlas quotient, represented
kernel-pair point lifting, finite connected closed-cover component formula,
constructible overlap image loci, and finite truth-pattern construction.

The two projections of `productAtlasMap` are the original chart after the first
scheme projection, and the second represented scheme projection. For any
represented base change `V`, kernel-pair incidence of the pulled-back cover is
equivalent to existence of an original kernel-pair point in the two cover
members whose base image belongs to the range of `V`.

In the forward direction, a common test scheme witnessing equality of the
base-changed chart images gives a common test for the original images after
the first projection. Represented pullback lifting supplies an original
overlap point, and the structure-map equations place its base image in the
range of `V`. In the reverse direction, the scheme pullback range theorem
supplies a point in the product of the original overlap with `V`. Its two
projections to the base-changed chart have equal chart images, producing the
required incidence. This argument needs neither finiteness nor closedness.

`geometricAtlasCoverSets s p` defines the inverse images of the original cover
members in the canonical algebraic-closure geometric atlas fibre. The
canonical geometric point has range exactly `{p}`. Hence
`geometricAtlasCoverIncidence_iff` identifies their geometric kernel-pair
incidence with membership of `p` in `atlasCoverIncidenceLocus`.

For a finite closed atlas cover whose geometric fibre pieces at `p` are
nonempty connected and covering, `geometricAtlasClosedCoverComponentsEquiv`
therefore computes the actual geometric fibre components as the quotient of
the fixed cover labels by these original overlap image predicates. Its target
uses exactly the presheaf product and `pointTopology` in the host statement.

The final theorem proves constructibility of every actual geometric component
count over a Noetherian ring for a quasi-separated space with a quasi-compact
locally finite-type surjective étale chart, provided a fixed finite closed
chart family is nonempty connected and covering on every geometric fibre.
Closed overlap image loci are constructible by `AtlasClosedCoverIncidence`;
the finite truth-pattern theorem gives constructibility of their quotient
counts; the preceding equivalence identifies those with the exact counts.

The final theorem retains the geometric connected-cover hypotheses. This unit
does not construct such covers by finite splitting and spreading, descend the
result from a splitting base, or perform arbitrary-ring approximation. It
therefore does not prove the unrestricted host target.
