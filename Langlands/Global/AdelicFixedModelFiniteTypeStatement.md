# Fixed-model adelic comparisons for finite-type arithmetic models

This derived target is the finite-type arithmetic specialization of
`AdelicFixedModelPointComparisonStatement`. Its source context is Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.6, equation (3.5.1) and its following Noetherian argument, together
with the final topology on printed p.9. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`.

For a finite-type scheme `X` over the original outside-`S` integer ring,
every actual full-adele point factors through a level at some finite
superset of `S`. The canonical map from the actual stage-point colimit is
bijective and is a homeomorphism for the two specified final topologies.
As in the general target, these use the original arithmetic stage topology
transported by the actual model base-change equivalence. Finite type is
expressed by local finite type and quasi-compactness of the structure map.
No affineness or separatedness of the model is assumed.

The function-field branch has the stated rational-function algebra and
scalar tower making `F` a function field over `k`. Constants need not be
finite or perfect, and the initial finite set `S` may be empty. The
number-field branch uses every number field and retains all infinite
completions in each full adele level. Both branches have arbitrary common
universe. In particular the result includes the global fields of either
characteristic required in Conrad's application.

The arithmetic ingredient is the proved Noetherianity of these actual
outside-`S` integer rings, `adelicSIntegersNoetherian`. The spectrum of a
Noetherian ring is locally Noetherian, so a locally finite-type structure
morphism is locally finitely presented. The general fixed-model comparison
then applies. This is why the target needs the function-field presentation
in the curve branch, rather than asserting Noetherianity for an arbitrary
field extension. Quasi-compactness records the source's finite-type scope;
the deduction of local finite presentation itself uses only local finite
type over this Noetherian base.

The target concerns the initial arithmetic model evaluated on the full
adele algebra. The generic-fiber equality at the right end of (3.5.1),
coherence with changing-base stage maps, independence of the initial model
and further topological conclusions remain separate obligations.
