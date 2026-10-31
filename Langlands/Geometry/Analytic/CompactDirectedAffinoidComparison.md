# Actual affinoid comparison for compact directed atlases

A compact space with an actual directed indexed affinoid atlas and a nonempty original chart index has a unique original chart covering the whole space. This module constructs that chart, its spectrum homeomorphism, and the bijection between full strong morphisms and actual bounded maps on the whole-chart algebras. In the universes supported by the published singleton realization, it also constructs a strong isomorphism with the singleton atlas of that actual affinoid algebra.

The coefficient field `K : Type u` is normed, ultrametric and complete. An `IndexedAffinoidAtlas.{u,v,w} K X` has ambient space in universe `v` and original chart index in universe `w`. Its algebras are actual `PresentedAffinoidAlgebra K` objects: quotients of finite positive-polyradius Tate algebras by their displayed closed ideals, with their constructed Banach structure. Chart maps embed their actual Banach spectra, restrictions are bounded algebra maps, and the domain universal property tests every presented affinoid algebra, including nonstrict ones. No reducedness or nonzero-algebra premise is imposed.

The original conventions are V. Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §1.1, printed pp. 13–14 / PDF pp. 10–11; Definition 1.2.3 and Remark 1.2.4(i), printed p. 16 / PDF p. 13; and Definition 1.2.7, printed p. 18 / PDF p. 15. The registered source is `berkovich-1993-etale-cohomology`, SHA256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`. These passages define the quasinet, actual affinoid atlas and full strong morphisms used by the imports. The compact directed comparison here is derived infrastructure under extra hypotheses; it is not a numbered assertion quoted from Berkovich.

`IndexedAffinoidAtlas.exists_range_eq_univ_of_compactSpace` applies `AtlasTopology.IsQuasinet.exists_subset_of_isCompact` to the compact subset `Set.univ` and the quasinet component of the actual atlas net. Directed quasinet compact containment puts the whole space inside one original chart range, so that range equals `Set.univ`. `existsUnique_range_eq_univ_of_compactSpace` uses the atlas's injective indexing of chart domains to prove uniqueness. `compactSpace_iff_exists_range_eq_univ` also proves the converse: a whole-space chart is a continuous surjection from its compact actual Banach spectrum, hence the ambient space is compact.

All three results retain `Nonempty a.Index`. An empty ambient space may have an empty original chart index, and compactness alone cannot produce an index in that case. An empty spectrum with an original chart is permitted. Directedness is also essential: the result concerns compact directed atlases, rather than all compact analytic spaces.

For `A : DirectedAtlasPresentation.{u,v,w} K`, with `CompactSpace A.presentation.space` and `Nonempty A.presentation.atlas.Index`, `compactTopChart A` selects the unique whole-space chart. Its presentation is definitionally the original presentation, as recorded by `compactTopChart_presentation`; it retains every original chart, algebra, restriction and domain test. `compactTopChart_range` proves its whole-space range, and `eq_compactTopChart_of_range_eq_univ` identifies any other original whole-space chart with it. The use of classical choice introduces no ambiguity in the selected index, by this uniqueness theorem.

`compactSpectrumHomeomorph A` is the actual spectral homeomorphism supplied by the published greatest-chart construction. Its domain is the Banach spectrum of the selected original chart algebra and its forward function is that chart map. `t2Space_of_compactSpace` derives global Hausdorffness from this homeomorphism and the Hausdorff property of the actual spectrum. No ambient Hausdorff assumption is added to the compact-containment step. `compactAffinoid A` is the opposite of the selected actual presented affinoid algebra, an object of `PresentedAffinoidSpace K`.

`compactTopChartIso A : ofTopChart A.compactTopChart ≅ A` reinterprets the original presentation as a directed object. Both maps are the full strong identity of that presentation. The two category equations are the published directed category identity laws; its directedness witnesses are propositions and do not alter the strong morphisms.

For compact directed objects `A,B` with nonempty original chart indices, `compactPullback f` is the bounded pullback at their whole-space charts for a full strong morphism `f : A ⟶ B`. `compactPullback_id` proves the bounded identity equation. `compactPullback_comp` first uses the published equality of directed and greatest-chart composition and then the greatest-chart pullback formula, giving the contravariant equation

`compactPullback (f ≫ g) = (compactPullback f).comp (compactPullback g)`.

`compactPullbackEquiv A B` is an explicit equivalence

`(A ⟶ B) ≃ BoundedAlgHom K (B.presentation.atlas.algebra B.compactTopChart.topChart) (A.presentation.atlas.algebra A.compactTopChart.topChart)`.

It uses `TopChartPresentation.topPullbackEquiv` on the constructed greatest-chart presentations. Its inverse uses the supplied bounded map on the whole-chart algebras, the source restrictions, and actual unique bounded domain factorizations to construct every admissible local pullback. `compactPullbackEquiv_symm_pullback_top` identifies the pullback at source chart `i` and the whole target chart as the source restriction followed by the supplied bounded map. `compactPullbackEquiv_symm_comp_restriction` identifies every admissible local pullback by its composite with the target restriction from the whole target algebra. These equations use algebra maps throughout, so information on nonreduced algebras is retained. Equality is not inferred merely from equality of point maps.

`compactSpectrumHomeomorph_naturality` states that the actual point map of `f` is the spectrum comap of `compactPullback f` in the two whole-chart coordinates. The chart, homeomorphism, bounded-map equivalence, composition formula and naturality result all retain independent `u,v,w`.

Finally, `compactAffinoidIso A` for `A : DirectedAtlasPresentation.{u,u,0} K` constructs

`ofTopChart (TopChartPresentation.ofAffinoid A.compactAffinoid) ≅ A`.

It maps the published greatest-chart singleton comparison isomorphism through `topChartFunctor` and composes with `compactTopChartIso A`. The equations `compactAffinoidIso_hom` and `compactAffinoidIso_inv` show that its two strong maps are exactly the published singleton comparison maps, because the final reinterpretation uses identity maps. Their whole-chart bounded maps are therefore the bounded identities from `TopChartAffinoidComparison`; the category equations retain the full compatible bounded families. The restriction to ambient universe `u` and index universe zero is the explicit universe boundary of that published singleton realization. No isomorphism with the singleton realization in arbitrary `v,w` is asserted.

This unit constructs the actual compact directed affinoid comparison. General analytic atlas extension, finite gluing, composition and localization for unrestricted atlases, structure sheaves, étale and equivariant sites, and the Harris tower remain separate obligations.
