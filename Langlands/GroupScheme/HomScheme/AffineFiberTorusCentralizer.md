# Geometry of torus centralizers with affine residue fibres

`AffineFiberTorusCentralizerGeometryStatement.{u}` concerns the actual closed
centralizer of a relative torus map into a smooth, separated, quasi-compact
group over a locally noetherian scheme. Assume the ambient group has affine
geometrically connected residue fibres and is affine after pullback to every
local Artinian affine test scheme. The chosen centralizer representative is
smooth, separated and quasi-compact and has affine geometrically connected
fibres.

For smoothness, apply the Artinian lifting criterion to the locally finite-type
structure map of the centralizer. Over the source of an elementary Artinian
thickening the ambient group is affine. Its centralizer is already known to
be smooth, and its actual representative is isomorphic to the pullback of the
original representative. Lift the point in this smooth pullback and project
back to the original centralizer. For geometric connectedness, base-change
to any field and use connectedness of torus centralizers in smooth connected
affine groups. Closedness of the inclusion gives affineness of each residue
fibre, and composition gives separatedness and quasi-compactness.

This implements the centralizer geometry used in the proof of Raynaud, SGA 3,
Exposé XV, Theorem 8.9(a), Gille–Polo recomposition, PDF p. 62, under the stated
affine test hypotheses. The Lean argument uses the Artinian lifting
criterion and field connectedness directly.
