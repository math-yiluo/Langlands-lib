# Functoriality of the constructed analytic point manifolds

This internal step of Conrad's Proposition 5.4 proves analytic functoriality of the canonical family for every actual algebraic-space morphism, including morphisms between different relative dimensions.

First, every topological inverse branch of an affine etale chart is analytic into the regular analytic manifold on its source. At a point, compare that branch with the chosen chart of the space; the common-refinement theorem makes the intervening branch transition analytic, and composition with the regular source chart inverse proves the source-chart criterion. Combined with analyticity of maps from smooth affine schemes, this packages the branch as a partial analytic diffeomorphism and shows that the actual point map is a local analytic diffeomorphism at its lifted point.

For a morphism `X → Y`, choose an affine etale lift of each rational point of `X`. The composite affine-scheme map into `Y` is analytic by the scheme-to-space theorem. Analyticity descends through the source chart's analytic local inverse. This proves `canonicalAnalyticPointStructure_isFunctorial`.

When `X` and `Y` have the same relative dimension and the space morphism is etale in the unchanged target's sense, composing the same affine source chart with it gives an affine etale chart into `Y`. Both its point map into `Y` and its point map into `X` are locally analytically invertible. Compose their partial diffeomorphisms with the source local inverse to prove `isLocalDiffeomorph_ringPointsMap` at the specified point. This proves `canonicalAnalyticPointStructure_isEtaleLocalIso`.

Affine-space normalization and uniqueness of admissible families remain separate obligations. These results retain every complete nontrivially normed field, every natural dimension and the original smooth algebraic-space hypotheses.
