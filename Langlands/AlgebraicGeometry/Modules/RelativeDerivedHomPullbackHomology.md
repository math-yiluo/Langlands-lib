# Pullback compatibility on sections cohomology

This internal supporting unit treats a commutative ring `R`, schemes `X` and `Y` over `Spec R`, an arbitrary morphism `f : Y ⟶ X`, a bounded below complex `K` of actual modules on `Y`, and every integer degree `n`. It compares the canonical relative pushforward/sections isomorphism with inverse image and the actual counit on the underlying abelian sheaves. No flatness, immersion, or exactness of module inverse image or direct image is assumed.

`relativeSectionsHomologyIso_pullback` identifies the underlying additive map on cohomology induced by `DerivedSections.pullbackSectionsComplexIso` through `sectionsHomologyIso`. On the Hom-complex side this is the composite of the homology map induced by abelian-sheaf inverse image, with the inverse constant-sheaf pullback comparison, and the homology map induced by `relativePullbackCounit`. The proof combines naturality of `DerivedPlusSource.localizedHomologyIso`, naturality of homology under exact scalar forgetting, and the previously proved chain identity `relativeSectionsComplexIso_pullback`.

`relativeComplexSectionsPullback` is the natural transformation obtained by applying localization and the underlying additive cohomology functor to the canonical relative pushforward/sections isomorphism on bounded below complexes.

`relativeComplexComparison_pullback` states the commuting square between `complexComparison` on `X` and `Y`, `relativeComplexSectionsPullback`, and `relativeComplexHomPullback`. The proof evaluates the square on an element, applies the preceding homology identity, and uses naturality and exact-functor compatibility of `EquivariantComposite.homologyDerivedMap`. This proves compatibility for the comparison defined directly on complexes. Extension to the right-derived comparison and the final assigned singleton cohomology statement remain separate obligations.

The provenance is internal: these are compatibility identities between the existing Library constructions, deduced from their naturality and the chain identity. No external mathematical assertion is being transcribed.
