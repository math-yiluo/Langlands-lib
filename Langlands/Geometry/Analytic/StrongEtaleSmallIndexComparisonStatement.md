# Étale recognition for small-index affine analytic presentations

`StrongEtaleSmallIndexComparisonStatement` isolates the universe profile of the recognition premise in `AffineAnalytificationLocalizedEtaleReductionStatement`. Let $K$ be a complete nontrivially normed ultrametric field of universe `u`. The source and target original affinoid atlas presentations have ambient spaces in universe `u` and chart indices in universe `0`. A strong morphism between their constructed saturations that is étale on all recognized pieces of the original presentations should satisfy the canonical `strongEtale` predicate of the saturated category.

The finite-polynomial-locus presentations of affine scheme analytifications have precisely this index universe. The canonical strong predicate tests the bounded pullbacks of the saturation extension. The statement expresses that passage to this presentation preserves the all-pieces condition across the index universes. Its conclusion is the premise needed to pass from the existing affine étale comparison to actual étale localized maps.

The analytic condition at a point comes from Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), Definition 3.3.4, p. 63. The universe comparison is internal to the Library's affinoid atlas implementation.
