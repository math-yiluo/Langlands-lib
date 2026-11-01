# Automatic local stabilizers on compact domains of open-chart atlases

## Provenance and scope

This is an internal construction by Worker 56. It combines the actual
original-domain covering condition and compact finite-point-cover
extraction of `OriginalDomainCompactCover` with the continuous action and
finite local-to-global stabilizer constructions of
`ChosenAtlasCompactOpenSectionAction` and
`ChosenAtlasCompactOpenSectionGluing`. The constructed disjoint affinoid
atlas supplies a concrete geometric example through its already proved
clopen chart ranges. No new claim is attributed to external literature.

The field is a complete ultrametric normed field. The atlas has its
actual quotient-spectrum charts, original subspace topologies and
original-chart domains. For the action results, `X` is a full chosen
bounded atlas action of a topological group, and `hX` is joint continuity
of its original point operator. The extra geometric hypothesis `hO` is
that every original chart range is open in the original ambient point
space. The point, chart-index, coefficient and group universes remain
independent of the field universe; coefficients are arbitrary types.

## Openness derived from open original charts

`IndexedAffinoidAtlas.isOpen_originalChartDomain` proves that every
original-chart domain is open under `hO`. At any point of the domain,
its original-domain quasinet supplies a finite relative-neighborhood
union of contained original charts. The point belongs to one of those
charts. That chart is open in the ambient space by `hO`, lies inside the
domain and contains the point. It therefore gives an ambient
neighborhood inside the domain. This proves openness without
compactness or ambient Hausdorffness.

`DisjointAffinoidAtlas.isOpen_originalChartDomain` applies this result to
the actual disjoint union of the spectra of any family of presented
affinoid algebras. Its constructed original chart domains are already
clopen, so no chart-openness hypothesis is supplied for this example.
Empty spectra remain omitted from the chart net exactly as in that
construction; no new nonemptiness assumption is introduced.

## Constructed finite original-chart point covers

For any compact original domain `S` and any full covering sieve `R` on
it, `OriginalChartDomain.compactSieveChartPointCover` constructs a finite
set of actual `SieveChart R` members. Each such member stores an
original chart contained in `S` and the fact that its original inclusion
belongs to `R`.

The construction applies the published
`IsCovering.sieveChartFamily` refinement theorem, followed by
`AtlasTopology.LocallyRefines.exists_finset_cover`. That compactness
argument collects finitely many original relative-neighborhood
witnesses and retains actual chart indices. The new
`compactSieveChartPointCover_covers` theorem rewrites its conclusion as
an indexed union over the subtype of selected members, with union
exactly the actual target subset `S`.

This extraction requires compactness, but no openness or Hausdorff
hypothesis. It is a finite point-cover statement. The full original
sieve keeps its original covering proof throughout the subsequent glue
construction; the finite extraction is used to determine the values of
that already constructed glue.

## Automatic common open stabilizers of whole glue

Fix a compact original domain `S`, an arbitrary full matching family `p`
on any covering sieve `R`, and a prescribed open subgroup `U` of the
original group. `openChartSieveGlue` pairs the actual whole
`OriginalDomainSection.sieveGlue p hp hR` with compactness of `S` and
openness derived from the original open charts.

`openChartGlueOpenStabilizer` first constructs the finite original-chart
point cover above. Each selected chart subset is compact because it is
the continuous image of its actual compact affinoid spectrum, and it is
open by `hO`. The selected whole locally constant functions are exactly
`p` evaluated at those original sieve inclusions. The preceding finite
stabilizer construction intersects all their full pair stabilizers with
`U`. Thus the result is a constructed open subgroup using actual local
sections; no finite selected cover is supplied by the caller.

`openChartGlueOpenStabilizer_le` proves that the constructed subgroup is
contained in `U`. `openChartSieveGlue_fixed` applies the preceding
finite local-to-global theorem using the extracted literal union
equality. The actual selected domain fixedness equations give invariance
of their union `S`, and their inverse-precomposition function equations,
together with the original glue recovery equations, give fixedness of
the entire glue pair. The wrapper's openness and compactness proofs can
differ from those derived by the finite theorem; proof irrelevance
identifies those witnesses while retaining the exact same domain and
whole function.

`openChartGlueOpenStabilizer_le_glue` gives containment in the entire
actual glue stabilizer. The construction supplies neither a global
fixedness premise nor a global glue stabilizer to be intersected. The
full matching family, original arbitrary covering sieve and original
point action are unchanged.

## Limits and empty cases

The open-chart hypothesis is a substantial geometric restriction. It is
proved for the constructed disjoint affinoid-spectrum atlas, and is not
asserted for general rational atlases, arbitrary analytic domains or
distinguished domains. The result constructs smooth locally constant
glue in this stated original-domain setting; it does not construct a
general equivariant sheaf category, all analytic or etale sites, or the
Harris tower.

Compact empty domains permit the selected finite family to be empty.
The construction retains empty coefficient types and empty covering
sieves whenever the given matching-family and covering data exist. It
uses no default coefficient value and requires no ambient Hausdorff
assumption.
