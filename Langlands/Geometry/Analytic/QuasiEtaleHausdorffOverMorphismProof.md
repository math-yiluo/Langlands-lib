# Morphisms over `X` into a Hausdorff space quasi-étale over `X`

Module `Langlands.Geometry.Analytic.QuasiEtaleHausdorffOverMorphismProof`. Everything is in the
namespace `Langlands.Analytic.SaturatedAtlasPresentation`. `K` is a complete ultrametric
normed field, and all objects lie in `LocalizedCategory.{u, v, v} (K := K)`.

The module proves `QuasiEtaleHausdorffOverMorphismStatement K` (module
`QuasiEtaleHausdorffStabilityStatement`), Berkovich's Lemma 3.1(ii) (*Vanishing cycles for
formal schemes*, Invent. Math. 115 (1994), §3, printed p.544, registered as
`berkovich-1994-vanishing-cycles-formal-schemes`) when the middle object is Hausdorff. Let
`g : Y ⟶ X` and `f ≫ g : Z ⟶ X` be quasi-étale, and let the underlying space of `Y` be
Hausdorff. Then `f : Z ⟶ Y` is quasi-étale. Nothing is assumed about `Z` or `X`.

More generally, the module proves the lemma whenever `g` has pointed local domain–étale
factorizations (`HasLocalDomainEtaleFactorizations g`, module `QuasiEtaleDomainLocality`). The
arrow `f ≫ g` only has to be quasi-étale in the Library's sense (`quasiEtale`, module
`QuasiEtaleSite`), whose charts need not contain the point.

## Results

- `exists_quasiEtaleCharts_of_hasDomainEtaleFactorization`. Let `ψ : L S ⟶ Z` be an arrow out
  of a saturated presentation `S`, `D` an analytic domain of `S`, `y ∈ D`. Suppose the
  restriction `S.localizedDomainInclusion D ≫ ψ` has a domain–étale factorization
  (`HasDomainEtaleFactorization`). Then there are finitely many charts of `S` that are
  quasi-étale charts for `ψ` (`IsQuasiEtaleChart`, module `LocalizedQuasiEtaleLocality`), and
  a neighbourhood `O` of `y`, such that `O ∩ D` lies in the union of their ranges.
- `exists_quasiEtaleCharts_cover_chart_of_comp`. Let `g : Y ⟶ X` satisfy
  `HasLocalDomainEtaleFactorizations g`, and let `i` be a chart of `presentationOf Z` such
  that `domainι Z (chartDomain i) ≫ f ≫ g` has a domain–étale factorization. Then the range
  of `i` is covered by finitely many ranges of quasi-étale charts for `f`.
- `quasiEtale_of_comp_of_hasLocalDomainEtaleFactorizations`: if
  `HasLocalDomainEtaleFactorizations g` and `quasiEtale (f ≫ g)`, then `quasiEtale f`.
- `quasiEtale_of_comp_of_t2Space`: if `Y` has a Hausdorff underlying space, `quasiEtale g`
  and `quasiEtale (f ≫ g)`, then `quasiEtale f`.
- `quasiEtaleHausdorffOverMorphism : QuasiEtaleHausdorffOverMorphismStatement.{u, v} K`: the
  same, for all `X`, `Y`, `Z`, `f`, `g`, with `T2Space (localizedSpaceFunctor.obj Y)` as an
  explicit hypothesis. This is the statement's exact form.

## Proofs

**First result.** This is the local step of `HasLocalDomainEtaleFactorizations.quasiEtale`
(module `QuasiEtaleDomainLocality`), stated for an arbitrary arrow `ψ` out of `S`. Write the
factorization as `j ≫ w` with `j` an analytic-domain embedding into `L W₀` and `w` étale.
`IsAnalyticDomainEmbedding.exists_local_affinoidDomainEmbeddings` gives finitely many charts
of the domain presentation `S.domain D` whose ranges cover a neighbourhood of `y` in `D`. On
each of them the restriction of `j` is an affinoid-domain embedding. A chart of `S.domain D`
is a chart of `S` contained in `D`. `exists_nestedChart_iso` (module `LocalizedChartTransport`)
identifies the two chart domains compatibly with the inclusions. Composing with this
isomorphism turns each chart into a quasi-étale chart of `S` for `ψ`, with the same étale `w`.
The neighbourhood of `y` in the subspace `D` is the trace of a neighbourhood `O` of `y` in the
space of `S` (`mem_nhds_subtype`).

**Second result.** Write `S = presentationOf Z` and `V` for the range of `i`. Let `x ∈ V`.
The hypothesis on `g` at the image of `x` gives finitely many analytic domains `D` of
`presentationOf Y`. Each contains the image of `x`, each has a domain–étale factorization of
`domainι Y D ≫ g`, and their union is a neighbourhood of the image of `x`. For each such `D`,
let `T = chartDomain i ⊓ domainPreimage f D`. This analytic domain of `S` contains `x`, and
`domainι Z T ≫ f` has a domain–étale factorization:

- `domainι Z T ≫ f ≫ g` has one, by restricting that of the chart
  (`HasDomainEtaleFactorization.of_domain_le`);
- `domainι Z T ≫ f` factors through `domainι Y D` (`domainOrderMap`, `domainPreimageMap`);
- `HasDomainEtaleFactorization.of_comp_of_factor` (module `QuasiEtaleOverMorphismReduction`)
  combines the two through the graph into the pullback of the étale envelope.

The first result applied to `T` gives finitely many quasi-étale charts for `f` and a
neighbourhood `O_D` of `x`. Let `O_x` be the intersection of the `O_D` with the preimage under
`f` of the union of the domains `D`. It is a neighbourhood of `x`, by continuity of the
underlying map of `f`. A point of `O_x ∩ V` maps into some `D`, so it lies in the
corresponding `T` and in `O_D`, hence in one of the charts chosen for `D`. The range `V` is
compact (`isCompact_range` of the chart embedding), so finitely many of the `O_x` cover it
(`IsCompact.elim_nhds_subcover`). The charts chosen for these finitely many points cover `V`.

**Third result.** By `quasiEtale_of_forall_isLocalizedQuasiEtaleAt` (module
`LocalizedQuasiEtaleLocality`) with `S = presentationOf Z`, it suffices to check the pointwise
condition `IsLocalizedQuasiEtaleAt` for `f` at every point `z`.
`isLocalizedQuasiEtaleAt_of_quasiEtale` gives finitely many quasi-étale charts for `f ≫ g`
whose union is a neighbourhood of `z`. These charts need not contain `z`. The affinoid-domain
embedding of each is an analytic-domain embedding
(`IsAffinoidDomainEmbedding.isAnalyticDomainEmbedding`), so the second result covers each of
their ranges by finitely many quasi-étale charts for `f`.
`IsLocalizedQuasiEtaleAt.of_cover` concludes.

**Fourth result.** `hasLocalDomainEtaleFactorizations_of_quasiEtale` (module
`QuasiEtaleDomainLocality`) gives `HasLocalDomainEtaleFactorizations g` for the Hausdorff
source `Y`; apply the third result.

**Fifth result.** Unfold the statement, introduce the Hausdorff hypothesis on `Y` as a local
instance and apply the fourth result.

## Why the charts of `f ≫ g` need not contain the point

The family that the third result builds at `z` consists of charts inside the ranges of the
given charts of `f ≫ g`. It covers each of these ranges entirely, not only near `z`. Its union
therefore contains the given neighbourhood of `z`, whether or not a given chart contains `z`.
This uses only that a chart range is compact.

The pointed hypothesis on `g` is not weakened in the same way. The graph factorization applies
to `f` only on pieces whose image lies in a domain of `g` with a domain–étale factorization, so
in the second result the charts for `f` lie inside the inverse images of those domains. If the
family of domains of `g` were only nonpointed, a domain that misses the image of `x` could
accumulate at it, and its inverse image in `V` need not be compact. A finite union of compact
chart ranges contained in a noncompact inverse image is compact, so it cannot be the whole
inverse image. Refining a fixed family of nonpointed domains of `g` in this way can fail to
give a neighbourhood of `x`. The Markdown of
`QuasiEtaleOverMorphismReduction` gives a doubled-disc configuration where no finite family of
compact charts, each contained in one of the two fixed inverse images, is a neighbourhood of
the point.

## Relation to the general statement

`QuasiEtaleOverMorphismStatement` (module `QuasiEtaleStabilityStatement`) asks for the
conclusion without a Hausdorff hypothesis on `Y`. The third result reduces it to
`HasLocalDomainEtaleFactorizations g` for every quasi-étale `g`, which is the body of
`QuasiEtaleLocalDomainFactorizationsStatement`. The reduction does not ask for the property
at `f ≫ g`, unlike `quasiEtaleOverMorphism_of_localDomainFactorizations` (module
`QuasiEtaleOverMorphismReduction`). This module does not prove
`QuasiEtaleOverMorphismStatement` itself. The Markdown of `QuasiEtaleOverMorphismReduction`
explains the obstruction to refining a fixed family of nonpointed charts and gives the two
literature routes for an arbitrary middle object.

## Scope

Standard axioms only. No compactness, smallness or chosen-limit hypothesis is placed on any
object. The only Hausdorff hypothesis is on `Y`, in the fourth and fifth results.
