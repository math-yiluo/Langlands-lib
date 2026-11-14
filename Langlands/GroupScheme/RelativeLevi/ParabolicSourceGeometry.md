# Geometry of sources of relative parabolics

This internal helper derives geometric connectedness of the source of a
relative parabolic from published field results. It introduces no additional
hypotheses on the base or on the inclusion.

For `i : P → G`, `IsRelativeParabolicSubgroup.geometricallyConnected` assumes
that `i` is a relative parabolic and that `G` is reductive, and proves that
`P → S` has geometrically connected fibres. The proof uses the criterion
that every residue fibre is geometrically connected. On each residue fibre,
`G` is connected reductive and the given fibre inclusion is parabolic. The
published field dynamic classification presents its range as a dynamic
parabolic. The dynamic connectedness theorem gives connectedness of the
actual source fibre. Smoothness and affineness come from the relative
parabolic hypothesis by pullback. The published smooth connected affine
group geometry theorem then upgrades this to geometric connectedness of
that residue fibre.

`relativeParabolicSourceGeometry` retains the actual group scheme `P` as
data with its smoothness, affineness and the proved geometric
connectedness. Its value lemma is definitional. This package supplies the
source geometry used by local containment arguments.

The result is derived from `RelativeLevi.Basic`, `Reductive.BaseChange`,
`Absolute.ParabolicDynamicProof`, `Dynamic.ConnectedProof` and
`SmoothConnectedGeometryProof`. All schemes and fields range over one
arbitrary universe. The base may be nonaffine, nonreduced, non-Noetherian
or disconnected, and the relative parabolic inclusion need not be assumed
globally closed.
