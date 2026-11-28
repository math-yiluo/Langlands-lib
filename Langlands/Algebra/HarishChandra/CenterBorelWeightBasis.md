# Joint weight bases for the center projection at a split Cartan

The joint weight spaces of the Cartan action span the Lie algebra
by the split Cartan hypothesis. Mathlib's independence of generalized
weight spaces also gives independence of actual weight spaces. The
proof collects bases of these spaces into a basis of the Lie algebra,
reindexes the finite basis by an ordinal, and sorts by decreasing
real part of the weights at the chosen Cartan element. Each nonzero
weight space is one-dimensional, so it has one basis vector whenever
it occurs.

The bracket of two joint weight vectors has the sum of their weights
by the Lie derivation identity. A joint weight vector has no coordinates
in other weight spaces, as follows by applying each Cartan action
to the coordinate functionals. Thus the positive root subspace is
the span of the basis vectors with positive real weight at the
chosen element. These derived facts supply the PBW order and weight
calculations for the center projection.

For a basis vector of nonzero weight \(\chi\), the split Cartan
supplies a root vector of weight \(-\chi\) as part of its bracket
data. The line condition identifies the chosen basis vector with
a nonzero scalar multiple of the corresponding vector of weight
\(\chi\). The bracket of the pair is therefore a nonzero Cartan
direction. Brackets of the same opposite vector with other root
basis vectors lie in nonzero weight spaces, so their Cartan
restrictions vanish.
