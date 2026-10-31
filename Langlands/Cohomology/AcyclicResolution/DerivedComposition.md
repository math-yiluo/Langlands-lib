# Derived composite comparisons through right resolutions

Author: Worker 606.

This internal extension proves identities for actual morphisms in derived
categories. It lifts the published degreewise identities in
`AcyclicResolution.Composition` and `ExactComparison` to the canonical
`derivedResolutionComparison`. All category, morphism and derived-category
universes remain arbitrary.

For additive functors `F : C ⥤ D`, `G : D ⥤ E`, `H : C ⥤ E` and a
specified natural isomorphism `e : F ⋙ G ≅ H`, assume `F` preserves finite
limits, the source categories have enough injectives, and the categories
have the indicated derived categories. Given a quasi-isomorphic augmentation
`ε : A[0] ⟶ K` whose mapped augmentation for `F` is also a
quasi-isomorphism, and vanishing positive right derived functors of `F` at
`A`, `derivedResolutionComparison_compComparison` computes
`derivedResolutionComparison H ε` followed by the actual
`derivedCompComparison G e A`. The result is the specified localized
termwise comparison `derivedCompResolutionIso G e K`, followed by the
derived comparison for the mapped augmentation.

The proof chooses an injective resolution `I` of `A` and the compatible
lift `t : K ⟶ I.cocomplex`. The mapped lift preserves the mapped
augmentation. Naturality of `derivedResolutionComparison` for that square,
together with naturality of `derivedCompResolutionIso`, identifies the
two composites. This needs no acyclicity assumption on the terms of `K`
or on the functor `G`.

For an additive `G : C ⥤ D`, exact additive `P : D ⥤ E`, and
`e : G ⋙ P ≅ H`, `derivedResolutionPostcompIso G P e K` is the specified
isomorphism from applying `P.mapDerivedCategory` to the localized extended
image of `G K` to the localized extended image of `H K`. It composes the
published `resolutionPostcompNatIso` with `resolutionCongrNatIso`.
Here exactness is expressed by preservation of finite limits and colimits.

`derivedResolutionComparison_derivedCompIso` states that applying the
induced exact functor to the resolution comparison, then the published
`DerivedPlus.derivedCompIso`, is this termwise isomorphism followed by the
resolution comparison for `H`. The proof computes both sides with the
same compatible lift to `I`, cancels the injective-resolution
identification, applies `derivedCompIso_hom_resolution`, and finishes by
naturality of the two termwise comparison isomorphisms.
`derivedResolutionComparison_inv_derivedCompIso` is the inverse form,
obtained by cancellation.

The provenance is internal: these identities use the published explicit
resolution models and their naturality, with the same comparisons as the
existing cohomology identities. They assert equality of the actual
derived morphisms, without inferring such equality from their maps on
cohomology. No geometric base-change or perfectness assertion is made here.
