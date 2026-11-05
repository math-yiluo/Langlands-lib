# Recognition of an original chart by its section equalizer

For a finite family of original affinoid charts with represented pairwise intersections, this module proves that the section equalizer recovers the algebra of an original chart whenever the literal union is exactly that chart. Both algebra maps and their bounds are constructed. The canonical finite-union spectrum map is then identified with the resulting homeomorphism.

## Source and scope

The original source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §1.2, printed pp.20–21 / PDF pp.17–18. The paragraph after Lemma 1.2.12 defines the Banach section algebra by overlap restrictions and invokes Tate acyclicity for independence of a special covering. The next paragraph and Proposition 1.2.13 use affinoid recognition to extend the original atlas. The source is registered as `berkovich-1993-etale-cohomology`, SHA256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

This is derived infrastructure for the original-chart case of that construction. Its proof uses the published finite full-domain algebra descent and bounded-map descent implementations, which pass through relative rational refinements and inverse norm estimates. The input family need not satisfy the source's additional admissible completed-tensor epimorphism condition for a special cover. Instead, its union is required to equal the range of a specified original chart, where all selected members and overlaps have the existing actual full-domain structures. No output algebra, inverse bounded map or homeomorphism is assumed.

The result concerns a finite cover of an existing original chart. It does not recognize an arbitrary finite union as affinoid, prove general special-cover independence, construct the maximal finite-gluing atlas or complete the general analytic-category comparison. Those remain separate obligations.

## Inputs and actual full-domain cover

The coefficient field `K : Type u` is complete and normed with ultrametric distance. The ambient topological space `X : Type v` and the chart-index universe `w` remain independent. The input `a : IndexedAffinoidAtlas K X` carries actual positive-polyradius Tate-algebra quotient presentations, embedded Banach spectra and bounded restrictions. Let `d : FiniteChartGluingData a`, `parent : a.Index`, and `hcover : d.locus = Set.range (a.chart parent)`.

`member_subset_parent` extracts containment of each selected range from this literal equality. `parentDomainCover` uses `a.restrictionDomain` to make each selected member a full domain in the original parent algebra. Its arrows to the whole domain are the stored original bounded restrictions. Its covering proof applies `hcover` to each parent-spectrum point and unpacks membership in the finite ambient union. Thus the cover and its original algebra carriers are constructed, rather than supplied as further input.

`parentDomainCover_projection_compatible` promotes the equalizer equations to compatibility after every full-domain test into two members. For such a test `W`, the represented original overlap defines an actual parent domain `O`. Its literal intersection equation shows `W.locus ⊆ O.locus`, giving the bounded inclusion `W → O`. The stored left and right restrictions give arrows from `O` to the two cover members. Full-domain arrow uniqueness identifies their composites with the original test arrows. Composing the full bounded-map equation `projection_overlap` with the restriction to `W` proves the required compatibility. This uses equality of bounded algebra maps, including information not visible on spectrum points.

## Constructed mutually inverse bounded maps

`glueToParent : SectionAlgebra → parent.algebra` is the actual bounded algebra map obtained by applying finite full-domain bounded-map descent to the equalizer projections and the proved test compatibility. `restriction_comp_glueToParent` recovers every full projection map. Boundedness is inherited from that descent theorem's proved inverse norm estimate; no open mapping theorem or nontrivial-valuation premise is introduced here.

`parentRestrictions_compatible` proves that the original parent restrictions satisfy the equalizer equations, using the original restriction-composition law through the overlap. `restrictFromParent : parent.algebra → SectionAlgebra` is the previously constructed bounded equalizer lift of this family. `projection_comp_restrictFromParent` recovers each original restriction.

`glueToParent_restrictFromParent` proves the first inverse law on all elements of the parent algebra by full-domain algebra separation and projection recovery. `restrictFromParent_glueToParent` proves the other by equality of all coordinates in the actual equalizer subtype. `parentAlgEquiv` packages these two constructed bounded maps and their inverse laws as `BoundedAlgEquiv K (a.algebra parent) d.SectionAlgebra`. The proof does not infer an algebra-map equality from equality of spectrum maps and makes no reducedness assumption. Empty families and repeated chart indices are not excluded; an empty family is subject to the same literal equality `hcover`.

## Identification of the canonical spectrum map

`parentHomeomorph` first identifies the literal union subtype with the original chart-range subtype using `hcover`, then applies the inverse of the original chart embedding's homeomorphism onto its range. It requires no Hausdorff assumption on `X`. `parentHomeomorph_componentMap` identifies its value on a selected chart with the comap of the stored restriction to the parent.

`spectrumMap_eq_parent` proves that the canonical pointwise `spectrumMap` from `FiniteChartGluingSpectrum` equals the inverse spectrum homeomorphism of `parentAlgEquiv` composed with `parentHomeomorph`. Surjectivity of the actual chart cover reduces the proof to one original chart. There, equality of seminorms follows by evaluating the full equation `restriction_comp_glueToParent` on a section.

`originalSpectrumHomeomorph` is the composite of these two constructed homeomorphisms. `originalSpectrumHomeomorph_apply` identifies its underlying function with the canonical finite-union spectrum map. Consequently that particular map is continuous and bijective onto the entire section spectrum in this original-chart case, without assuming either property. General finite-union recognition remains outside the conclusion.
