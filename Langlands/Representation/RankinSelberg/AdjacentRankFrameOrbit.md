# Compact open orbits of rectangular frames

This internal geometry supports the adjacent-rank compact-section spanning
step. The frame of an invertible matrix of size `n+1` is its first `n` rows,
equivalently `[I,0]g`. The module proves its multiplication law, its
compatibility with left multiplication by `GL_n`, and its full row rank,
expressed by a matrix right inverse. No positivity assumption on `n` is
needed. The algebraic results use an arbitrary field.

For the actual ordered shape `(r+1,1)`, vanishing of the final column above
the final row characterizes membership in the lower parabolic. The frame of
such an element `q` is `[a(q),0]`, where `a` is the actual large-block
projection. Conversely a frame `[h,0]` proves lower membership and identifies
that projection with `h`. For any ambient subgroup `J`, the exact orbit
criterion is

`[h,0]g ∈ frame(J) ↔ ∃ q ∈ P, j ∈ J, g=qj and a(q)=h⁻¹`.

For the forward direction, the frame of `g j⁻¹` is `[h⁻¹,0]`; the converse
uses the published rectangular multiplication formula for the actual lower
parabolic. This retains all `r`, including zero.

Over a Hausdorff topological field, the frame map is continuous. Its image of
an identity neighborhood contains a neighborhood of `[I,0]`: append the final
standard row to a nearby frame and use the open embedding of invertible
matrices into all square matrices. Right translation then proves that the
frame image of an open subgroup is open. A compact subgroup has compact
image. Consequently a compact open subgroup supplies an actual
Schwartz–Bruhat indicator whose entire topological support has full row rank,
and hence an element of `adjacentRankCompactTests`. Right multiplication by
an element of the subgroup preserves its frame image, so the constructed
test is right invariant under that whole subgroup.

The inner slice `adjacentRankFrameSlice J` is the subgroup
`a(P ∩ J)` of `GL_(r+1)`. Its membership condition is exactly
`[h,0] ∈ frame(J)`. If `J` is compact open, this slice is open by continuity
of `h ↦ [h,0]` and openness of the frame image. It is closed because it is an
open subgroup. The already proved compact-orbit support theorem makes the
restriction of the frame indicator compactly supported on `GL_(r+1)`.
Every point of the slice has indicator value one, so closedness makes the
slice compact.

This is derived matrix and topological content, following the published
`LastRowCompactOrbitProof` neighborhood construction with the first `n` rows
in place of the last row, and reusing `AdjacentRankCompactOrbit` for inner
compactness and `AdjacentRankLowerParabolic` for the literal block algebra.
No external result beyond these imported formalized constructions is invoked.
The module asserts no section spanning, integral identity or model-image equality.
