# The norm-continuous Banach contragredient

`NormContinuousDual.space R` consists of the bounded complex-linear functionals
whose inverse-precomposition orbit is continuous at the identity in the
operator norm. `NormContinuousDual.representation R` restricts the action to
this invariant subspace. Its evaluation satisfies
`(representation R g L).val v = L.val (R g⁻¹ v)`.

`NormContinuousDualStatement` applies to a jointly continuous representation
on a complex Banach space of the units of a finite-dimensional real Banach
algebra. It gives closedness of the norm-continuous subspace, joint continuity
of the restricted action, and a functional in that subspace taking a nonzero
value on each nonzero original vector. The subspace inherits completeness from
the continuous dual. The algebra and representation carrier have independent
universes.

## Proof

Continuity of an orbit at the identity gives continuity everywhere by group
translation. Right translation of the orbit gives invariance of the subspace.
On a compact neighborhood, the original action has a uniform operator norm
bound, and the norm of inverse precomposition is at most the norm of the
operator for the inverse element. These local bounds control the error when
an original functional is approximated in the operator norm by functionals
with continuous orbits. This proves closedness. The same bounds control the
variable-functional term in the evaluation action, and the fixed-functional
term is continuous by the orbit property. The closedness and joint-continuity
arguments work on any locally compact topological group.

For separation, Hahn–Banach supplies a bounded functional positive on the
given nonzero vector. The real part of its orbit coefficient is positive
near the identity. Use `smoothNormalizedInverseKernel` to choose a nonnegative
compactly supported kernel in this neighborhood. Precompose the functional by
the corresponding averaging operator for right Haar measure. By
`continuousAt_smoothedOperator_comp_inv`, right translates of the averaging
operator are continuous in operator norm at the identity, so this precomposition
belongs to the norm-continuous part. Its evaluation has positive real part by
the integral of the nonnegative weighted coefficient, which is positive at the
identity.

The construction uses the bounded inverse-precomposition action of
`SmoothDualEvaluation` and the Banach smoothing estimate of
`RightKernelOperatorContinuity`. It gives the continuous dual realization
needed when applying the regularization of dual norms to a Banach realization
of a Harish–Chandra module.
