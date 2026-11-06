# Compact convex affine facet closures

This independently derived helper proves that closures of facets of an
essential affine root system are compact and convex in a finite dimensional
real normed vector space. The hypotheses are the existing
`IsAffineRootSystemWithRankZero`, including derivative spanning and corrected
infinite discrete fibers; no positive rank hypothesis is imposed.

Weak sign regions are closed intervals, half-lines or singletons. Their affine
preimages express each facet closure as a closed convex intersection. In each
derivative fiber, finiteness of bounded values and infinitude give a root with
large absolute value at a chosen point. Coroot reflection and negation produce
another parallel root with the opposite sign there. These two root inequalities
bound that derivative coordinate throughout the facet closure.

Evaluation on the derivative roots is an injective linear map, because those
derivatives span the full dual. Its finite dimensional source makes it a closed
embedding. The coordinate bounds put the facet closure in the inverse image of
a compact product of closed intervals, so its closedness proves compactness.
This is a new argument assembled from the existing root-system axioms and
Mathlib topological and linear algebra results.
