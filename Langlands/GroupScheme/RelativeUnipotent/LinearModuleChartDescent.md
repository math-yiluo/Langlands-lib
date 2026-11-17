# Descent of point charts with an actual linear module cocycle

This is an internal construction for the relative unipotent filtration project.
All schemes and their module sheaves are in an arbitrary universe `u`. Let
`p : X ⟶ S`, let `F` be an actual module sheaf on `X`, let `D : Datum p F`
be an actual geometric module descent datum, and let `V` be a group scheme
over `S`.

`LinearModuleCharts D V` records, for every test `T` over `S` with a lift
`a : T.left ⟶ X`, a multiplicative equivalence between the actual points
`T ⟶ V.X` and the multiplicative presentation of the actual global sections
of `a`-pullback of `F`. Its naturality equation uses `pullbackSection` and
the canonical pullback-composition comparison. Its compatibility equation
uses the actual module-sheaf isomorphism `D.θ` for every pair of lifts with
the same composite to `S`. Thus a genuine linear module cocycle is supplied;
linearity is not inferred from additive point-group comparisons.

For any effective structure `Q : Str D (𝟙 S) M`, `chartIso` is its actual
module isomorphism from the pullback of `M` to the pullback of `F` on a
lifted test. `sectionIsoEquiv` takes global sections of an actual module
isomorphism, yielding an additive equivalence.
`toLocalSectionCharts` composes the given point chart with the inverse of
this section equivalence. The resulting charts take values in the
pullbacks of one fixed downstairs module `M`. The proof
`chartIso_sectionPullback` obtains their precise naturality from `Q.nat`,
the canonical composition isomorphisms and pullback-section naturality.
The equation `Q.coc`, together with `LinearModuleCharts.compatible`, proves
independence of the lift.

`IsFiniteLocallyFree.of_iso` transports actual finite local frames along a
module-sheaf isomorphism. With `p` flat, locally of finite presentation and
surjective, `finiteLocallyFree_of_str` applies this transport to the actual
isomorphism `pullbackIsoOfStr D Q` and then applies the proved
`hasFiniteLocalBasis_of_pullback_fppf`. Thus finite local bases of `F`
give finite local bases of `M`. Their sizes may vary between charts.

The final theorem `LinearModuleCharts.isVectorBundleAdditive` assumes that
`p` is affine, flat, locally of finite presentation and surjective, that `F`
is `IsFiniteLocallyFree`, and that `V.X.hom` is affine and smooth. It proves
exactly `RelativeUnipotent.IsVectorBundleAdditive V`. Finite local bases
first supply quasi-coherence of `F`. The published theorem
`GeometricQuasicoherentDescent.exists_str D (𝟙 S)` supplies an actual
quasi-coherent module `M` and effective structure `Q`. The finite-local-basis
reflection just described and the proved fixed-module chart-descent
construction then supply the actual module witness, all-test
multiplicative equivalences, and their naturality for the exact
`RelativeUnipotent.sectionPullback` in the target.

The provenance is the existing geometric module-effectivity theorem, finite
local basis reflection, fixed-module section-chart descent, and elementary
transport along the module isomorphisms. No additional effectivity premise,
affine-base hypothesis, noetherian hypothesis, common rank, or nonempty-base
hypothesis is imposed. The hypotheses on the cover and the supplied charts
remain explicit. Constructing the required charts from relative parabolic
geometry and assembling the parent radical filtration remain separate
obligations.
