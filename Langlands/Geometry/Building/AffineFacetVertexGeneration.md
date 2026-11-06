# Vertices generate compact convex facet closures

This internal helper defines the actual vertices incident to a root facet using
the existing zero-dimensional-facet predicate. For a locally finite reflection
arrangement on a real normed vector space, every extreme point of a facet closure
is such a vertex. Local constancy of all nonzero root signs supplies a short
symmetric segment in the facet of any proposed nonvertex; the roots vanishing at
its center vanish along that segment. This contradicts extremality.

Consequently a compact convex facet closure is the closed convex hull of its
actual vertices, by Mathlib's Krein–Milman theorem. A continuous affine map fixing
those vertices fixes the whole closure: its fixed set is closed and convex.
Setwise fixation of every incident facet implies fixation of every vertex and
therefore the same pointwise conclusion.

This argument is independently derived content. Compactness and convexity are
explicit hypotheses here and are not inferred from local finiteness alone (which
also admits unbounded arrangements). The module constructs no building metric
and identifies no building subgroup with a pointwise fixer. Those applications
must prove compactness, convexity and the face-fixing premise from their original
data. There is no positive-rank or nonempty-root assumption.
