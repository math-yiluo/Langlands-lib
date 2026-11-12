# Injectivity of the analytic differential of unramified affine maps

Author: Worker 115.

All charts are supplied `Analytic.RegularChart`s on actual affine scheme
points over an arbitrary complete nontrivially normed field `k : Type u`.
The source and target dimensions may differ in this module.

`RegularChart.contDiffAt_inverse_evaluation` uses the open chart target to
specialize the inverse-evaluation analytic field to any point in that target.
`tangent_eq_zero` proves that a vector killing every such regular evaluation
is zero. Each chart coordinate is the quotient of its numerator and denominator
evaluations. Near a target point, that quotient equals the corresponding
coordinate projection, by the two chart identities. The chain rule through
the pair of evaluations shows that its derivative kills the vector; the
derivative of a coordinate projection therefore gives each component zero.

`coordinateMap c c' f` is the actual point map of the relative affine scheme
morphism `f` read in these charts. `contDiffAt_coordinateMap` proves it
analytic when the inverse source point lies in the target chart source.
Actual point-map continuity gives eventual containment in that source;
its coordinates are locally quotients of inverse-source-chart evaluations
of the pulled-back target numerators and denominators.

`coordinateMap_fderiv_injective` assumes only `FormallyUnramified f.left`.
For a vector in the kernel, each target regular function along the actual
point map is locally its inverse-target-chart evaluation composed with the
coordinate map. The chain rule therefore shows that the evaluation derivation
of the inverse source chart kills the pulled-back target coordinate algebra.
The preceding module's formal unramifiedness lemma forces it to kill the
entire source algebra. `tangent_eq_zero` gives that the vector is zero.

The proof is an internal connection between the existing algebraic and analytic
APIs. It adds no separability, characteristic, point-nonemptiness or
positive-dimension premise, and it does not assume an etale local-inverse theorem.
