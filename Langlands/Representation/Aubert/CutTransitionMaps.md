# Aubert transition maps indexed by cuts

Author: Worker 164.

This internal helper identifies the shape order needed by the actual Aubert
diagram. It adds no exactness or effectivity assumption or conclusion.

If the cut set of `B` is contained in the cut set of `C`, equality of two
`C` block indices implies equality of their `B` block indices, by the
published cut-side criterion. Monotonicity of consecutive block indices
then shows that a strict separation by `B` blocks remains strict for `C`.

The module reuses `Langlands.Geometric.mem_parabolic_iff_blockIndex` from
`StandardIntersectionsProof` and states the unipotent-radical matrix
membership criterion in ambient coordinate indices. A parabolic has zero
entries when the column block precedes the row block. A radical matrix
has the corresponding identity-matrix entries whenever the column block
is at most the row block. These criteria show that adding cuts shrinks the
actual parabolic and enlarges its actual upper radical, over every
commutative ring, including rank zero.

`Transition.cutMap` applies the actual pointwise quotient transition from
`TransitionMaps` to those two proved inclusions. Its identity and
composition laws are exactly the previously proved laws; proof
irrelevance identifies the subgroup-inclusion witnesses. Thus this is the
actual normalized induction–Jacquet diagram on shapes ordered by cuts.

This is a derived GL coordinate implementation of the standard-parabolic
inclusions behind the maps in Ban–Jantzen, *The Langlands quotient theorem
for finite central extensions of p-adic groups II* (2016), section 4,
printed p.159. The cited registered source is
`ban-jantzen-2016-duality`, SHA-256
`7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`.
The concrete proof uses the Library's published cut and actual matrix
criteria, rather than an additional subgroup-order premise.
