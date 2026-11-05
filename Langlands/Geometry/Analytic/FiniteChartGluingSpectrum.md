# The literal finite-union map to the Banach section spectrum

This module constructs the map from a literal finite union of original affinoid charts to the spectrum of its constructed Banach section algebra. It proves independence of the chart representative, the exact image and the formulas for section evaluation and bounded comaps. It also proves continuity when the actual finite chart cover is a quotient map, and in particular whenever this union is Hausdorff.

## Source and scope

The original source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §1.2, printed pp.20–21 / PDF pp.17–18, the paragraph after Lemma 1.2.12. It defines the Banach section algebra of a special subset using a finite special covering, asserts independence of the covering, and constructs the continuous map to its spectrum. The following paragraph and Proposition 1.2.13 impose additional conditions for affinoid recognition and the maximal atlas.

The present module is derived infrastructure for the map in that paragraph. It uses `FiniteChartGluingData` and its actual Banach equalizer from `FiniteChartGluingAlgebra`. These inputs require represented pairwise intersections but do not require the source's admissible tensor-product epimorphism condition for a special covering. Consequently, the pointwise construction is made for all such data, while continuity retains an explicit topological hypothesis. Neither represented intersections alone nor compactness of a subset of an arbitrary space is used to infer Hausdorffness or quotient topology.

The source is registered as `berkovich-1993-etale-cohomology`, SHA256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`. Cover independence, the general special-domain continuity argument, affinoid recognition and maximal-atlas extension remain separate obligations. The module does not assert injectivity or surjectivity onto the entire section spectrum, or supply an affinoid algebra as output.

## Literal cover and representative independence

The coefficient field `K : Type u` is complete and normed with ultrametric distance. The ambient topological space `X : Type v` and chart-index universe `w` are independent. Let `a : IndexedAffinoidAtlas K X` and `d : FiniteChartGluingData a`. The type `d.locus` is the subtype of the literal finite union in `X`, with its inherited topology. Its `CompactSpace` instance comes from the already proved compactness of that finite union.

`componentMap i` sends a point of the original chart spectrum to its ambient chart point in this union. Its continuity follows from the original chart embedding. `totalMap` is the resulting continuous map from the finite disjoint union of the original spectra. `totalMap_surjective` unpacks membership in the literal union, so the cover is proved from the existing ranges.

`spectrumFamilyMap` uses the bounded coordinate projections of the constructed equalizer to map each original spectrum continuously to `BanachSpectrum d.SectionAlgebra`. The imported literal-overlap agreement proves `spectrumFamilyMap_factorsThrough`: two representatives with the same image under `totalMap` have the same image in the section spectrum.

`spectrumMap` chooses a preimage under the proved surjection and applies this local spectrum map. `spectrumMap_componentMap` uses fiber agreement and the right-inverse equation to recover every original local spectrum map. `spectrumMap_comp_totalMap` gives the resulting commutative diagram, and `spectrumMap_unique` proves that these local equations characterize the pointwise function. These constructions and equations require no Hausdorff or continuity hypothesis on the union. They include an empty family and repeated chart indices.

## Exact continuity criterion

`continuous_spectrumMap_of_isQuotientMap` proves continuity from `IsQuotientMap d.totalMap`. The proof uses the quotient-map continuity criterion and the already continuous map on the finite disjoint union; it does not assume a continuous global map as input.

When `d.locus` is Hausdorff, the finite disjoint union of compact original spectra is compact, and the continuous surjection `totalMap` is closed and hence quotient. This proves `totalMap_isClosedMap` and `totalMap_isQuotientMap`. `continuous_iff` then characterizes continuity of any function from the union to any topological space `Y : Type z` by continuity of its composites with all `componentMap i`.

`continuous_spectrumMap` applies this result to the constructed function, and `spectrumMapContinuous` packages it as a continuous map. `spectrumMapContinuous_componentMap` is the equality of continuous maps on each original chart. The Hausdorff assumption is on this finite union alone; no separation hypothesis on the ambient `X` is introduced.

## Image and evaluation

`range_spectrumMap` proves that the image is exactly the finite union of the images of the original `chartSpectrumMap i`. Surjectivity of the actual chart cover and the local recovery equations prove both inclusions. Thus `isCompact_range_spectrumMap` follows from compactness of the finitely many local images, even when global continuity has not been established. Since the Banach spectrum is Hausdorff, this also proves `isClosed_range_spectrumMap`.

`spectrumMap_componentMap_apply` evaluates a section at a point represented in chart `i`: its value is the original seminorm applied to the actual coordinate `projection i s`. For any normed commutative test `K`-algebra `S : Type z` and bounded map `f : S → d.SectionAlgebra`, `comap_spectrumMap_componentMap` identifies its spectrum comap on that point with the comap of the full bounded composite `(projection i).comp f`. Both formulas reduce to the constructed local spectrum maps; neither infers an algebra-map equality from an equality of point maps.
