# Generic specialization of full normalized induction

Worker 1444, adapting Worker 1635's published compact-open specialization proof.

This derived helper exposes the group-generic argument already implemented privately
in `RationalNormalizedInducedSpecializationProof.lean`. It constructs the canonical
complex-linear equivalence `UnramifiedNormalized.inducedSpecializationEquiv` from the
fiber of the full universal normalized induced module to the full complex induced
module. On pure tensors it is `z ⊗ f ↦ z • inducedEvaluation f`. It retains closedness
of the parabolic subgroup, continuity of every indexed norm character and the Levi
projection, and compactness of the literal left quotient. It assumes no root
presentation, finite-dimensional coefficient space or admissibility.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, VI.8.2, printed pp.190–191 / PDF pp.196–197, especially (VI.8.2.2)
and the specialization corollary. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This is an internal extraction of its published proof route, not a new proof
of any unproved representation-theoretic prerequisite.

The coefficient fixed-space comparison reuses the public
`RationalNormalized.tensorFixedEquiv`. Tensor cancellation then identifies
specialization of its fixed-space evaluation with the identity of the complex
fixed space. Finite compact-open double-coset evaluation and the finite-product
tensor equivalence give bijectivity on each compact-open fixed module. Tensor
induction places every fiber element in the image of one such module; an
intersection handles sums. The commuting square with the inclusion of target
fixed vectors proves full injectivity, without assuming that tensoring an
inclusion is injective. Smoothness and fixed-level surjectivity give full
surjectivity. Compact stabilizers annihilate the unramified twist, so this
argument applies to the complete positive-half-modulus normalized inducing
actions. The resulting equivalence uses exactly the existing coefficient and
function-value evaluation maps.
