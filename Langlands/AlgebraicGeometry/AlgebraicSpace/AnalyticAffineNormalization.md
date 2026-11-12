# Affine-scheme comparison and affine-space normalization

This internal construction compares the canonical space-point manifold with the published regular manifold on an actual smooth affine scheme. The scheme-to-space point equivalence is bijective and locally analytically invertible at every point, by applying the affine chart theorem to the identity chart. Hence it is an analytic diffeomorphism.

On actual affine space, the global-section algebra equivalence and polynomial point homeomorphism give the usual coordinate homeomorphism. Its coordinates are regular evaluations, so it is analytic for every regular analytic atlas. Each regular evaluation of its inverse is a polynomial evaluation, which proves inverse analyticity by the regular-evaluation criterion.

`affineSpaceCoordinateDiffeomorph` composes the inverse scheme-to-space comparison with that affine coordinate diffeomorphism. Its underlying function is proved equal to the unchanged target's `affineSpaceCoordinates` on every rational point. The required algebraic relative dimension of affine space is recovered from the supplied `IsSmoothPureDimensional` hypothesis using its identity etale scheme chart.

`canonicalAnalyticPointStructure_agreesWithAffineSpace` packages the normalization, and `canonicalAnalyticPointStructure_isAdmissible` combines it with the already proved analytic manifold, functoriality and etale local-isomorphism properties. Thus this file proves the entire existence half of the unchanged `AnalyticPointManifoldStatement`. The uniqueness half remains an obligation; no conclusion of uniqueness is claimed here.
