# Actual finite selected-atlas realizations of original local full domains

Author: Worker 36.

For a locally refining selection of original charts, this module constructs
a finite gluing datum in the selected atlas's actual local-domain saturation
for every original local full domain. The given old domain algebra and
ambient map realize this datum. The component algebras are the chosen
saturated-chart algebras, and the overlaps use actual affinoid pushout
quotients. Every bounded restriction and its compatibility is constructed.

## Source and provenance

This is derived infrastructure for Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Proposition 1.2.13(i)–(ii),
printed p.21 / PDF p.18. The registered source is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original page was read for this construction; no source-specific
errata file was found in the available Library location.

Part (i) compares completed domain families under passage to a subnet.
Its proof reduces the comparison to finite subordinate covers of old
charts. Part (ii) extends the atlas by canonical bounded restrictions.
The present construction is an internal step toward those conclusions,
under the explicit `IsLocallyRefiningSelection` hypothesis. The source
does not separately state this chosen-presentation realization.
The module uses the constructed finite selected pieces and the proved
comparison of full bounded restrictions under the subatlas forget
functor. It supplies no output recognition or algebra comparison as
an additional hypothesis.

## Full components over an original local domain

Write `b = a.subatlas P hP`, where `a` is the original indexed atlas and
`hP : a.IsLocallyRefiningSelection P`. Let `U : LocalDomain a` and
let `S` be an index of `b.saturatedAtlas` whose chart range is contained
in `U.locus`.

The saturation chooses an actual `b`-local-domain presentation for `S`.
`subatlasSaturatedInclusion` forgets its selected-parent proof and applies
the original atlas's canonical local-domain inclusion construction to
obtain an actual arrow to `U`. Its bounded restriction is constructed
from full affinoid-domain universal properties.
`subatlasSaturatedComponent` takes this arrow's relative full-domain
representation over `U.algebra`.

`subatlasSaturatedComponent_algebra` states the definitional equality
between this component algebra and `b.saturatedAtlas.algebra S`.
`subatlasSaturatedComponent_locus` identifies its precise locus with

```text
U.ambientMap ⁻¹' range (b.saturatedAtlas.chart S).
```

`subatlasSaturatedComponent_over_ambient` identifies the component's
ambient map with the actual saturated chart, using the inclusion's
ambient naturality.

For any contained pair `S ⊆ T` of these chart ranges,
`subatlasSaturatedComponent_naturality` proves equality of the entire
bounded maps from `U.algebra` to the algebra at `S`. The saturated
inclusion `S → T` is mapped by the subatlas forget functor. Its composite
with the canonical inclusion `T → U` equals the canonical inclusion
`S → U` by uniqueness of actual original local-domain inclusions.
Applying their stored restrictions and using the forget functor's
proved full restriction comparison gives the desired equation.
This covers every contained selected-saturation chart, not merely a
finite list, and does not infer algebra-map equality from spectrum maps.

## Finite selected charts and actual overlaps

Now let `c : a.SelectedChartCover P parent` be a finite selected-chart
cover of an original chart, and let
`U : Domain K (a.algebra parent)` be any full domain.
The imported finite-cover construction supplies actual selected local
pieces whose loci cover the old local domain `⟨parent, U⟩`.
Such a `c` is constructed from `hP` by `a.selectedChartCover`.

`saturatedDomainIndex` regards each selected piece locus as an index
of `b.saturatedAtlas`. `saturatedDomainIndex_range` recovers exactly
that locus, and `saturatedDomainIndex_subset` proves containment in
the old domain. `saturatedDomainComponent` uses the preceding general
construction, with parent algebra `U.algebra`. Its locus and
ambient-map theorems specialize the general component formulas.
The algebra is therefore the saturation's actual chosen quotient
algebra, regardless of which local presentation its choice selects.

For two components `E` and `F`, `saturatedDomainOverlap` forms the
actual full-domain intersection `E.inter F` over `U.algebra`.
This is the affinoid pushout quotient of their structural bounded maps.
It expresses the intersection as a relative domain over `E.algebra`
using its actual left inclusion and extends it through the chosen
selected local-domain presentation of the first component.
Relative representation and extension retain the actual intersection
quotient algebra.

`saturatedDomainOverlap_locus` proves that this selected local domain's
literal locus is exactly the intersection of the two saturated chart
ranges. The proof factors its ambient map through the old domain,
uses the relative domain's exact image formula, and substitutes the
component preimage loci. For the reverse containment it obtains a
preimage in the old domain from the first component's containment.

## Realizing the finite gluing datum

`saturatedDomainGluing` packages the finite component indices and these
literal overlap loci as `FiniteChartGluingData b.saturatedAtlas`.
The overlap-range equation follows from the saturation's range formula
and the proved overlap locus equality.
`saturatedDomainGluing_locus` proves that the finite union is precisely
the old local domain's locus, by the selected pieces' coverage.

`saturatedDomainAffinoidRealization` constructs every field of the
realization. Its algebra is the unchanged `U.algebra`, and its chart is
the unchanged old domain ambient map. Their embedding and range
properties come from the actual full domain. The component maps are
the constructed bounded structural maps, their full representations
use the exact preimage locus formula, and their chart equations are
the component ambient formulas.

For an overlap, the two instances of
`subatlasSaturatedComponent_naturality` identify the left and right
bounded composites with the same canonical restriction from the old
domain. Their equality proves the realization's full bounded
compatibility. No realization, section-algebra equivalence or
recognition of the old domain is supplied as an input.

## Hypotheses and scope

The field is complete and ultrametric, with explicit `NormedField`,
`IsUltrametricDist` and `CompleteSpace` instances. Its valuation may
be trivial. The field, ambient space and chart index have independent
universes. The ambient topology is arbitrary subject to the actual
atlas assumptions; global Hausdorffness is not added. The finite
cover may be empty when its coverage equation permits it.
No reducedness or nonzero-algebra assumption is used.

This unit constructs the finite realization and proves its bounded
compatibility. Completed-tensor overlap admissibility, specialness
of this cover, recognition of the old domain for the selected
saturation, and recognition invariance remain subsequent steps.
The full arbitrary equivalent-net theorem, maximal-atlas uniqueness,
unrestricted analytic morphism identification, analytic etale and
equivariant sites, and Harris specialization remain further obligations.
