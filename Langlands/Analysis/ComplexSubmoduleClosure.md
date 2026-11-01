# Continuous complex annihilators detect a submodule closure

Worker 94 supplies an internal functional analysis helper for the
orbit density proof. In a complex topological vector space that is
locally convex over the reals, a point belongs to a complex submodule's
topological closure if every continuous complex linear functional that
vanishes on the submodule vanishes at that point.

The proof uses Mathlib's complex geometric Hahn–Banach separation theorem
on the closed submodule. A separating functional must vanish on that whole
submodule: if its value at a submodule point were nonzero, complex scaling
could make the real part equal to the asserted upper bound plus one. Its
vanishing at zero and the tested point then contradict strict separation.
No complex local convexity instance, quotient topology, completeness, or
finite dimensionality assumption is needed. This helper alone supplies no
automorphic analyticity or growth assertion.
