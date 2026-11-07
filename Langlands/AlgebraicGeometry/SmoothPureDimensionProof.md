# From smooth chart dimension to actual pure fibre dimension

`smoothPureDimension` proves exactly
`Langlands.AlgebraicGeometry.SmoothPureDimensionStatement` in arbitrary
common universe `u`. Its two conclusions identify fixed standard-smooth
chart dimension with actual componentwise pure dimension over a field
and on every actual residue-field fibre of a scheme morphism.

This is a derived geometric comparison for the third proof paragraph of
Theorem 4.5 in Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed p.12. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The target's paired Markdown explains this provenance and the retained
arithmetic spreading obligations.

The implemented proof first bounds the Krull dimension of any scheme
stalk by the topological Krull dimension of the scheme. Mathlib
identifies stalk dimension with the coheight of its point; the order
isomorphism between scheme points and irreducible closed subsets
transports this coheight to the poset defining topological dimension.
The general coheight bound then applies.

For a nonempty quasi-compact scheme smooth of fixed chart dimension `n`
over a field, choose a closed point. The published
`fieldSmoothClosedPointStalkDimension` gives stalk dimension `n`, so the
preceding bound gives the global lower bound. The published
`fieldSmoothTopologicalKrullDim` supplies the upper bound. Consequently
every nonempty affine smooth neighbourhood has dimension exactly `n`.
Restriction to a source open preserves the fixed chart dimension by
composition with its open immersion, which has relative dimension zero.

The public helper `fieldSmooth_topologicalKrullDimAt` removes global
quasi-compactness. An affine neighbourhood of the chosen point gives
the upper bound on local topological dimension. For the lower bound,
choose an open neighbourhood whose dimension realizes the local
dimension, then choose an affine neighbourhood inside it. The latter
has dimension `n`, which is at most the dimension of the former by the
inclusion embedding. Both bounds prove that the local topological
dimension at every point is `n`. The published
`hasPureDimension_iff_topologicalKrullDimAt_eq_locallyOfFiniteType`
converts this into pure dimension for the actual irreducible
components. Ordinary smoothness supplies local finite type.

Finally, base change of fixed chart smoothness along
`Spec κ(y) ⟶ Y` makes the actual fibre structure morphism smooth of the
same chart dimension. The proof applies
`MorphismProperty.IsStableUnderBaseChange.of_isPullback` to the actual
fibre pullback square, using Mathlib's fixed-dimension stability
instance. The field result applies to this residue-field scheme and
gives the second conjunct.

The theorem imposes no affineness, separatedness, quasi-compactness,
surjectivity or connectedness hypothesis. Empty schemes and empty
fibres satisfy componentwise pure dimension vacuously. Nonemptiness is
used only for the intermediate quasi-compact dimension calculation.
This proof does not construct arithmetic models, choose a finite set
of places or prove the remaining Lang–Weil and adelic openness results.
