# Proof of relative affineness descent

Worker 105 proves the exact proposition
`Langlands.AlgebraicGeometry.AffineLimit.RelativeAffinenessDescent`
with `relativeAffinenessDescent`, in arbitrary universe `u`. This is the
derived relative-affineness clause of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed pp. 5–6,
Theorem 3.4(2). The statement's Markdown explains the weakening from
finite presentation to a qcqs relative morphism with quasi-compact
target over an affine base. This proof preserves arbitrary nonaffine
and nonseparated source and target schemes.

The helpers establish actual pullback squares for `baseChangeMap`,
base-changed chart squares, diagram transitions, cone projections, and
the comparison between a limit morphism and a stage morphism. They use
pullback pasting and cancellation. The copied `baseChangeCover` is an
actual open cover whose objects are the pullbacks of the original chart
schemes. The chart squares transport affineness in either direction,
and locality at the target recovers relative affineness from affine
chart sources.

The helper `exists_isAffine_level` applies Mathlib's
`Scheme.exists_isAffine_of_isLimit` to the published target base-change
diagram and its proved `isLimitCone`. Its objects are qcqs by base
change of the structural morphism; its transitions are affine by the
Cartesian transition squares, since both coefficient schemes are
affine. An affine limiting source therefore gives an affine stage.

For the forward implication, the coefficient limit is affine by
`Scheme.isAffine_of_isLimit`. Quasi-compactness of the target over the
affine base gives a finite affine open cover. The inverse image of each
chart under the relative morphism has qcqs structural morphism to the
base. If the limiting relative morphism is affine, its inverse image
over each base-changed affine chart is affine. Structural descent finds
a level for each chart. Cofilteredness gives one common level; its maps
to the chosen levels induce affine chart transition maps. Their targets
are affine, so their sources are affine. Locality of `IsAffineHom` on
the base-changed target cover gives the required affine relative
morphism at that common level.

For the reverse implication, the Cartesian comparison between the
limit morphism and the given affine stage morphism identifies the
former as a base change of the latter. Stability of `IsAffineHom` under
base change finishes the proof.

This unit proves only relative-affineness descent. It does not prove
the other properties in Conrad 3.4(2), initial-model existence, a
spectral or arithmetic adapter, or any statement about point topologies.
