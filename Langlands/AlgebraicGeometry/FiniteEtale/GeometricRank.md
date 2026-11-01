# Actual geometric fibres and native finite-flat rank

This internal bridge connects the actual section and coordinate-dimension comparison in `GeometricCardinality` to Mathlib's existing `Scheme.Hom.finrank`. It introduces no alternative notion of degree.

`fibreSectionsEquiv` identifies sections of the actual pullback of a morphism along a point with actual lifts of that point. The maps are the first pullback projection and the pullback lift with identity second component. The pullback equations prove the inverse identities.

`homFinrank_eq_coordinateFinrank` applies to any finite flat scheme over a field. Its scalar structure is exactly `coordinateAlgebra` of the actual structure morphism. The proof presents the affine source by its canonical spectrum isomorphism, identifies the morphism with the spectrum of its actual scalar map, and uses Mathlib's rank formula for spectrum maps. Rank at a prime of the field is the dimension of the free vector space. No separable closedness or étaleness is required for this equality.

`natCard_sections_eq_homFinrank` combines this equality with the proved finite étale section-count comparison over a separably closed field. `natCard_lifts_eq_finrank` then uses `fibreSectionsEquiv` and the native base-change invariance of rank. Its point fibre consists of actual scheme morphisms satisfying the displayed equation. It allows the empty fibre, whose count and rank are both zero.

The provenance is the actual pullback universal property and the directly used Mathlib finite-flat rank theorems. This comparison computes neither the rank of a polarized endomorphism nor the numerical rank of abelian torsion.
