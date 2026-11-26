# A linear pushforward from an ultrametric ball

`map_restrict_closedBall_linear`: let `X` and `Y` be proper normed spaces over a
nontrivially normed field, with `X` ultrametric, and let `μ` and `ν` be additive
Haar measures. For a surjective continuous linear map `d : X → Y` and a closed
ball `B` of positive radius in `X`, the image `d(B)` is compact and open, and
`d` sends `μ` restricted to `B` to `c • ν` restricted to `d(B)` for some
`c ≥ 0`.

A positive-radius closed ball about zero is an open additive subgroup (by the
ultrametric inequality), and it is compact because `X` is proper. Its image
under `d` is a compact open additive subgroup, open by the open mapping theorem.
On the two subgroups, the pullbacks of additive Haar along the open embeddings
are Haar measures. The map between the subgroups is a continuous surjective
homomorphism from a compact group, so its pushforward of the source Haar is
again Haar, and uniqueness of Haar measure on the compact image gives the
constant. Mapping back along the subgroup embeddings turns the pullbacks into
restrictions.

For a ball with arbitrary centre `a`, translate the ball about zero by `a` and
its image by `d(a)`. Translation invariance of `μ` and `ν` gives the formula at
that centre.

This lemma is used by `compactSubmersionPushforward` in
`Langlands.HarmonicAnalysis.CompactSubmersionPushforward`.
