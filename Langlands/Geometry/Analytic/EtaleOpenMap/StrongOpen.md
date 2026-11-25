# Openness of strong maps flat over all affinoid pieces

This is a derived proof of the flat quasifinite openness
argument used for Berkovich (1993), Proposition 3.2.7, printed p.59.

The implemented proof shrinks the finite source neighborhood of a flat point
inside any prescribed neighborhood using `IsFiniteOver.exists_small`. The
new recognized pieces are clopen subsets of the old ones. Their restriction
maps are flat, so the composition theorem for pointwise flatness preserves
flatness at the distinguished point.

Choose finitely many recognized target pieces containing the image point,
with union a neighborhood. On each piece the Noetherian finite Banach
image-neighborhood lemma applies. The embedding of its chart converts the
spectral neighborhood to an ambient neighborhood relative to that piece.
Intersect these finitely many ambient neighborhoods and intersect with the
union of the pieces. The resulting neighborhood lies in the image of the
prescribed source neighborhood.

Thus a map flat over all pieces at every point is open. An étale map in
`IsEtaleAllPieces` has this flatness at every point by its definition. The
proof uses the existing finiteness implicit in that pointwise flatness
predicate; no additional global separation or compactness assumption is made.
