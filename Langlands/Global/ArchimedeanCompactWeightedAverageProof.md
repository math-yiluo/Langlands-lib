# Weighted compact averaging in the actual derivative topology

Author: Worker 94.

`Langlands.Global.ArchimedeanGL.compactWeightedAverage` proves exactly
`CompactWeightedAverageStatement K n` for every number field in arbitrary
universe and every natural rank, including zero. The measure is any
finite measure compatible with the actual compact subgroup's Borel
topology; the weight is any continuous complex function.

The proof chooses `CompactWeightedAverage.averageCLM`. Its construction
first integrates the actual scalar functions `w(k) f(x k)`. The published
compact linear parameter integral theorem supplies smoothness and the
first derivative in matrix coordinates. A simultaneous finite derivative
expansion, proved by tensor and enveloping quotient induction, supplies
the exact scalar integral formula for every genuine enveloping derivative.

Continuity of scalar averaging for the compact-open topology and those
finite derivative expansions prove continuity in the full derivative
topology. The resulting continuous complex linear endomorphism has the
required evaluation formula `eval_averageCLM`.

Finally `average_mem_closed_compactOrbit` uses finite collections of
compact derivative restrictions. Their weighted orbit integrals lie in
the closed image of the compact-orbit span in a finite product of Banach
spaces. The scalar derivative integral formula identifies these integrals
with the restricted coordinates of the actual average. The topology is
induced by all these coordinates, so the finite-coordinate closure
criterion yields the required closed compact-orbit membership.

This is an internal derived proof following the constructions described
in the four helper modules. It requires neither an integral in the
smooth-function carrier nor completeness of that carrier. It asserts no
character orthogonality, projector range identification, admissibility,
reproduction or automorphic differential growth. Independent review and publication of this proof remain separate from
compilation.
