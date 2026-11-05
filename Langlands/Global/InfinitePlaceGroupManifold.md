# The constructed manifold of actual infinite-place group points

Author: Worker 94. This internal assembly specializes the actual scalar-extension
manifold and Lie-group construction to an infinite-place completion. It uses the
published `InfiniteCompletionRCLike` construction of Worker 1359 by import.

Let `F` be a field in any universe, let `G` be an affine group scheme over `F`,
and let `v` be an actual infinite place of `F`. Assume
`SmoothOfRelativeDimension d G.X.hom` for a natural number `d`. The explicit
constant-dimension hypothesis is retained; smoothness alone is not substituted
for it. No `NumberField F` hypothesis is needed for this local construction.

`completionRCLike F v` pins the compatible `RCLike` choice from
`v.completion_isRCLikeNormedField`. Mathlib's compatible-choice constructor
retains the original completion normed field definitionally, including its norm,
metric and topology. The choice is passed explicitly in the definitions and
statements because the original field is not inferable from the opaque completion
carrier during global instance search.

`smoothChartedSpace` installs the exact `affineBaseChangeChartedSpace` on
`InfinitePlaceGroupPoints F G v`, the original relative-morphism point group over
`v.Completion`. Its topology is the original regular-function evaluation topology.
The charts are pulled from the named General affine charts of the actual base
change of `G` to `v.Completion`, using the actual scalar-extension homeomorphism.
The model is `Fin d → v.Completion`, viewed as a real normed vector space.
`smoothIsManifold` and `smoothLieGroup` specialize the proved base-change results;
the latter uses the existing multiplication and inverse of the original point
group. No replacement carrier or independent pre-existing atlas is assumed.

`contMDiff_iff_coordinateSmooth` identifies ordinary real manifold smoothness of
an arbitrary family `p` into this local group with smoothness of every original
regular-function value in `v.Completion`. The parameter space may be any charted
space with its own real model with corners and independent universe; it need not
be a manifold. The criterion tests all elements of the original coordinate ring
of `G` before base change.

`contMDiff_iff_realCoordinates` and `contMDiff_iff_complexCoordinates` use the
specified Mathlib ring equivalences from the actual completion to `ℝ` and `ℂ`
under `IsReal v` and `IsComplex v`, respectively. Both statements concern real
differentiability. The proof converts each ring equivalence's additive equivalence
to a continuous real-linear equivalence using continuity of the supplied isometry
and its inverse. Composing with the resulting diffeomorphism preserves and
reflects smoothness of every regular-function value. This proves compatibility
with the actual test maps without equating the chosen `RCLike` structure or
separately chosen atlases with other choices.

The provenance is internal assembly of the published completion comparison,
the actual affine-point base-change manifold and Mathlib's continuous additive
to real-linear equivalence construction. The unit constructs the local
archimedean manifold and original Lie group under the stated algebraic hypothesis.
The finite infinite-adelic product, constant-dimension existence for connected
reductive groups, reduction theory, differential growth and automorphic Hilbert
spaces remain separate constructions.
