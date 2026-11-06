# Extensionality and functorial laws of equivariant horizontal transport

This internal unit derives congruence, identity and composition laws for the
published `Horizontal.mapCyclesIntertwiner` and
`Horizontal.mapCohomologyIntertwiner`. The source and target are the existing
horizontal kernels and cycle quotients with their given monoid actions; no
new coefficient, cohomology or representation object is substituted.

The two congruence lemmas apply function extensionality to equal families of
bundled cochain maps, substitute the equal family, and use proof irrelevance
for the possibly different chain-compatibility witnesses. The `_id_of_eq`
lemmas combine congruence with the published identity law. The
`_comp_of_eq` lemmas combine congruence with the published composition law.
Thus these conclusions require the displayed equalities of the actual
cochain families, rather than any representation-theoretic identification.

All field, Lie algebra, three coefficient, group and monoid universes remain
independent. The only characteristic assumption is the explicit `CharZero`
used by the underlying horizontal differential. This is an internal
derivation from the existing construction, with no external-source claim.
