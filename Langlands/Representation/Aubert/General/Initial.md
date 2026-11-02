# The canonical initial map of the normalized complex

Internal construction by Worker 194, using the normalized comparison
from Worker 23 and the existing orbit-function construction.

`augmentation A s` transports the canonical orbit function through the
normalization equivalence. Its value at `g` is exactly the class of `g v` in
the actual `U(s)`-coinvariants. The comparison with the unnormalized orbit
function proves its naturality and compatibility with all quotient transitions.

There is exactly one removed-root set of cardinality zero, the empty set.
`degreeZeroEvaluation` extracts that coordinate; the proof that it is bijective
uses `Finset.card_eq_zero`. `initialMap` sends an input vector to the orbit
function in every degree-zero coordinate. Under the explicit endpoint identities
`P(∅) = G` and `U(∅) = 1`, the previously proved full-group/trivial-radical
augmentation bijection gives `initialEquiv`. Its forward map is the actual
`initialMap`, not an arbitrarily chosen isomorphism. The degree-zero map is
natural in ambient smooth morphisms.

`initialDifferential` composes the initial map with the signed differential from
degree zero to degree one. Its square with the next differential vanishes by the
already proved signed square-zero law. These are intrinsic construction laws on
actual subgroup families. Their endpoint hypotheses still need the shared
standard-parabolic realization. They assert no exactness of the truncated
complex and impose no finite-length assumption.
