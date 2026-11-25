# The varying-dimension analytic manifold assertion

The theorem
`Langlands.AlgebraicGeometry.AlgebraicSpace.smoothSourceAnalyticManifold`
proves the unchanged published proposition
`Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceAnalyticManifoldStatement.{u}`
for every universe `u`.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points*, December 31, 2011, Proposition 5.4, printed p.15, with the analytic
construction in the final proof paragraph on printed p.16. The registered
original is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad allows the dimension of the smooth space to vary. The published target
uses the corrected class of smooth, quasi-separated, locally separated
algebraic spaces; affine-space normalization, functoriality and étale local
analytic isomorphisms encode agreement with the scheme case.

For a complete nontrivially normed field `K`, the proof obtains
`hK : PointTopology.IsHenselianValuedField K` from the published
`PointTopology.completeHenselianValuedField K`. Let
`σ := canonicalAnalyticPointStructure K`. The published
`canonicalAnalyticPointStructure_isAdmissible K` supplies admissibility of
this pure-dimensional family. Choose `σ.dimensionStructure hK` as the
varying-dimension family.

Its atlas on each eligible space is definitionally `σ.dimensionAtlas hK`.
The proof supplies the four conjuncts of
`DimensionAnalyticStructure.IsAdmissible` using the published theorems:

- `smoothSourceDimensionAnalyticAssembly`, applied to the analytic component
  of `σ`'s admissibility, proves analytic transitions;
- `smoothSourceDimensionAnalyticFunctoriality` proves analyticity of every
  morphism's actual point map in every pair of source and target charts;
- `smoothSourceDimensionEtaleAnalyticIso` proves intrinsic dimension
  preservation and local branches analytic in both directions for étale maps;
- `smoothSourceDimensionAffineAgreement` proves that the actual affine-space
  coordinate equivalence and its inverse are analytic.

These are proved inputs, with no extra hypotheses left on the final theorem.
The proof then applies `smoothSourceDimensionAnalyticUniqueness K` to conclude
that every two admissible varying-dimension families are equivalent.
This uniqueness quantifies over all such families, and means that the actual
identity of each rational-point space is analytic in both directions.

This final assembly is a derived organizational step using the published
dimension-piece proofs. The analytic charts remain on the original
`RingPoints K X K` with `etaleChartTopology K X`, and cover all intrinsic
natural-number dimensions, including zero and empty pieces. No
quasi-compactness, global pure dimension, finite dimension range or additional
separation hypothesis is introduced. Completeness is used to obtain the
canonical admissible pure-dimensional family and henselianity; the final
statement covers both archimedean and nonarchimedean complete fields.
