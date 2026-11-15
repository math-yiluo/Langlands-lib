# Actual Čech transitions and coordinate reindexing

This internal construction develops coherent comparisons for the actual Čech
datum in `Descent.Data`. It uses the published `pullbackComparison`,
`pullHom_eval` and `pullHom_pullHom` interfaces. Every scheme lies in the same
arbitrary universe. No covering, flatness, affineness, reducedness or
quasi-compactness hypothesis is imposed on any map.

`pullbackComparison_assoc` identifies the two actual group-scheme morphisms
that remove three successive pullbacks. The proof compares their projections
to the original total group scheme and their structure maps to the final base.

For a map `q : V → S` and two maps `f,g : T → V`, `reindexHom` and
`reindexIso` convert a supplied comparison between the direct pullbacks of
actual groups along `f ≫ q` and `g ≫ q` into a comparison between the two
pullbacks of their groups over `V`. They conjugate the supplied comparison by
the canonical iterated-pullback isomorphisms. `reindexHom_comp` states
preservation of composition. `pullHom_reindexHom` states compatibility with
every further pullback, with the endpoint equalities explicit; its proof uses
the associativity comparison and inverse cancellation.

For an actual `D : Datum p G`, `Datum.transition f g h` constructs the actual
group-scheme isomorphism between the pullbacks of `G` along any maps `f,g`
with equal composites with `p`. It pulls `D.overlap` back along the induced
map to the double overlap. `pullHom_transition` identifies its further
pullback with the transition on the new pair of maps.

`transition_comp` proves composition of these transitions on every test
scheme. The implementation constructs the map to the triple overlap, pulls
back `D.cocycle`, and removes iterated comparisons using
`pullHom_pullHom`. Thus the composition equation is proved from the original
actual cocycle, rather than included as another input.

These are comparison and transition constructors for supplied data. They
prepare restriction of Čech data to affine refinements, but this module does
not construct a reindexed `Datum`, any effective descent solution, a pinning,
or a quasi-split inner form. It does not prove the host existence statement.
