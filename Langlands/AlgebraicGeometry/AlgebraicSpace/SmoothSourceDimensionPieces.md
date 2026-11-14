# Actual algebraic dimension pieces of arbitrary smooth spaces

Author: Worker 502.

This derived host bridge supports Brian Conrad, *Weil and Grothendieck
approaches to adelic points*, December 31, 2011, printed p.15, Proposition 5.4.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The dimension pieces are derived supporting content, not a separate numbered
assertion in that source.

For any field `K` and any actual algebraic space `X` over `Spec K` with
`hX : SmoothOverBase X`, `SmoothDimensionPieces.subset hX n` is the level set
of the intrinsic `pointDimension hX` at each natural number `n`. Local
constancy from `SmoothSourcePointDimension` proves it both open and closed
in the actual ordinary quotient point topology. Every natural number is
retained, including empty pieces, without compactness or finite range.

`space hX n` and `inclusion hX n` reuse `PointOpenSubspace.space` and
`PointOpenSubspace.inclusion` from `SmoothDimensionOpenSubspaces`. Their
subfunctor consists of actual sections whose entire ordinary point image is
in the level set. The inclusion is a representable open immersion, its exact
ordinary-point image is the selected level set, and these images cover and
are pairwise disjoint.

`restrictedAtlas` is the actual open subscheme of the chosen smooth atlas
over the level set, constructed by `PointOpenSubspace.chartScheme`.
`restrictedAtlasInclusion` is its open immersion into the old atlas.
`restrictedAtlasMap` is the actual `Subfunctor.lift` through the point-selected
subfunctor. `PointOpenSubspace.range_chartInclusion` identifies its image on
every test scheme, and
`OpenSubfunctorLifting.isPullback_subfunctor_of_range` proves the atlas square
cartesian. Base change therefore supplies etaleness and surjectivity.

The restricted structural morphism is smooth because it is an open immersion
followed by the old smooth structural morphism. Its source is locally
Noetherian since it is locally of finite type over the field. The
all-chart theorem `pointDimension_chart` computes its local relative
topological Krull dimension as `n` at every point. The published
`smoothOfRelativeDimension_of_localDimension` from
`SmoothDimensionRestrictions` turns this into
`SmoothOfRelativeDimension n`, including empty sources. Thus
`space_hasAtlasProperty` supplies an actual restricted atlas of the required
fixed dimension, and `space_smoothOverBase` records structural smoothness.

Quasi-separatedness passes from `X` by
`OpenSubspaceGeometry.isQuasiSeparated_openSubspace`. Local separatedness
passes by the cartesian diagonal square for a monomorphism
(`OpenSubfunctorImages.diag_isPullback_of_mono`) and base-change stability
of represented immersions. Consequently `space_isSmoothPureDimensional`
inhabits the existing `IsSmoothPureDimensional K n` interface whenever `K`
is nontrivially normed and quasi-separatedness and local separatedness of
`X` are supplied separately. No completeness hypothesis is needed.

This unit supplies actual algebraic pieces, inclusions and restricted scheme
atlases. Actual field-valued section factorization and the all-natural-index
sigma equivalence are a separate construction unit. The homeomorphism for
the etale-chart rational-point topology, functorial analytic assembly across
target dimension pieces, etale dimension preservation, analytic local
isomorphisms and uniqueness of a varying-dimensional analytic structure
remain subsequent statement and proof obligations. This does not claim the
full manifold assertion.
