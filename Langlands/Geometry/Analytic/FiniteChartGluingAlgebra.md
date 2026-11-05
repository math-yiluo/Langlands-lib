# Banach section algebras for finite original charts

This module constructs the actual Banach algebra of compatible tuples on a finite family of original affinoid charts with represented pairwise intersections. It proves the bounded universal property and constructs continuous spectrum maps from the individual charts. The construction uses the existing chart algebras and bounded restrictions; it does not take a section algebra or an affinoid structure on the union as input.

## Source and scope

The original source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §1.2, printed pp.20–21 / PDF pp.17–18. The paragraph immediately after Lemma 1.2.12 defines the commutative Banach section algebra as the kernel of the difference of the two overlap restrictions. The following paragraph constructs a continuous map from the special subset to its spectrum, and Proposition 1.2.13 uses an additional affinoid-recognition condition to construct the maximal atlas.

The present construction is derived infrastructure for that paragraph. It forms the same kernel as an equalizer subalgebra, for any finite original-chart family whose pairwise intersections are represented by original charts. These inputs do not include the additional admissible tensor-product epimorphism condition in the source's definition of a special covering. No claim that every finite family is special is made. Cover independence, the global continuous map on the union, affinoid recognition, maximal-atlas extension and the general analytic-category comparison remain separate obligations. In particular, the module does not assert that the union is affinoid or that the spectrum maps are embeddings.

The registered source is `berkovich-1993-etale-cohomology`, SHA256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

## Inputs and the literal finite union

The coefficient field `K : Type u` is complete and normed, with ultrametric distance. The ambient space `X : Type v` and the index universe `w` are independent. The input `a : IndexedAffinoidAtlas K X` carries actual finite positive-polyradius Tate-algebra quotient presentations, embedded Banach spectra, and actual bounded restrictions satisfying the original chart equations and restriction laws.

`FiniteChartGluingData a` contains a natural number `size`, the original chart index for each `i : Fin size`, and an original overlap index for each ordered pair `(i,j)`. Its equation `overlap_range` identifies the overlap chart's actual range in `X` with the intersection of the two original ranges. It supplies no output algebra or spectrum identification. Chart indices may repeat, the family may be empty, and empty intersections are permitted when represented by an original chart. A family with an unrepresented intersection is outside these data.

`locus` is the literal union of the selected chart ranges in `X`. `isCompact_locus` follows from compactness of each actual spectrum and the finite-union theorem. `overlap_subset_left` and `overlap_subset_right` extract the two inclusions from `overlap_range`. `leftRestriction` and `rightRestriction` apply the existing stored restrictions to exactly these inclusions; their domains and codomains are the actual original algebra carriers.

## Closed equalizer and Banach structure

`Product` is the dependent finite product of the selected chart algebras, with its maximum norm. `sectionSubalgebra` consists of the tuples `s` for which

```text
leftRestriction i j (s i) = rightRestriction i j (s j)
```

for every ordered pair. The zero, unit, addition, multiplication and scalar laws are proved from the algebra-homomorphism laws of both restrictions. In particular, this is the kernel of their additive difference without treating that difference as an algebra homomorphism.

`isClosed_sectionSubalgebra` expresses the carrier as an intersection of equality loci. Coordinate evaluation is continuous, each restriction is continuous by its proved bound, and the overlap algebra is Hausdorff. Thus every equality locus is closed. `SectionAlgebra` is this actual subtype with its inherited normed commutative `K`-algebra structure. Its `CompleteSpace` instance follows from closedness in the finite product of complete original quotient algebras; its ultrametric distance is inherited from that finite product. These arguments include the empty product.

`projection i` is the evaluation algebra map restricted to the equalizer. Its bound is one, proved by the finite-product norm inequality. `projection_overlap` is equality of the complete bounded maps to the actual overlap algebra, using the equalizer equations. `section_ext` detects equality of elements by all coordinate projections.

## Full bounded universal property

Let `S : Type z` be any normed commutative `K`-algebra. No completeness, ultrametric, nontriviality or reducedness assumption on `S` is used. `MapCompatible f` requires equality of the complete composites of bounded maps `f i : S → A_i` with the two overlap restrictions.

`lift f hf` sends each `s : S` to the compatible tuple `(f i s)`. The algebra map is constructed by the dependent-product algebra map and restriction of its codomain to the equalizer. To prove boundedness, the implementation chooses a positive bound `M i` for every component and uses `(∑ i, M i) + 1` as a positive common bound. Each component bound is at most this number, so the maximum norm of the tuple satisfies the required estimate. This also gives a positive bound when `size = 0` and does not invoke an open mapping theorem.

`projection_comp_lift` recovers each full bounded component map. `hom_ext` proves that any two bounded maps into `SectionAlgebra` are equal when all their component composites are equal, and `lift_unique` proves uniqueness of the constructed lift. `boundedHomEquiv` packages the resulting equivalence between all bounded algebra maps `S → SectionAlgebra` and the subtype of compatible families. Its inverse is the constructed bounded lift, and both inverse equations are proved from the component recovery and extensionality.

## Spectrum maps and ambient overlap agreement

`chartSpectrumMap i` is the actual continuous contravariant spectrum map induced by the bounded projection. `chartSpectrumMap_overlap` proves that the two maps agree after comapping a point of the actual overlap spectrum. The proof evaluates the full equality `projection_overlap` at a section and then at the overlap seminorm.

`chartSpectrumMap_eq_of_chart_eq` gives agreement whenever two original chart points represent the same point of `X`. The literal intersection equation produces a point of the overlap spectrum. The stored restriction chart equations and injectivity of each original chart identify its two comaps with the given points, reducing the result to `chartSpectrumMap_overlap`. This direction uses full bounded-map compatibility to prove equality of spectrum points. It never infers equality of algebra maps from equality on spectrum points.
