# Simultaneous finite-stage realization of an absolute star equivalence

Worker 838. This is an internal prerequisite for the reverse implication of
`InnerFormStarActionStatement`, derived by combining the published common finite
Galois splitting field of two tori with the published finite-stage comparison of
star actions. The simultaneous assertion makes no additional source claim.

`CommonFiniteStageStarEquivalenceStatement` is a Prop-valued definition. For two
affine groups of locally finite type over an arbitrary field, two supplied
Galois pinning data over its separable closure, and a based equivalence of their
root data intertwining every absolute star action, it asserts the existence of
one finite Galois extension. Over that extension there are Galois pinning data
for both original groups and a based root-datum equivalence intertwining the
star actions of every element of the finite Galois group. The assertion
quantifies over every universe. It requires no adjoint quotient or chosen group
isomorphism.

The theorem `commonFiniteStageStarEquivalence` proves this statement. Each ground
torus is a torus because it splits over the separable closure. The published
`IsTorus.commonFiniteGaloisSplitting` provides one finite Galois field splitting
both. After embedding that field in the separable closure, the proof applies
`StarActionFiniteStage.exists_stage` to each group with the same field. The
finite-stage root equivalence is the supplied absolute equivalence conjugated
through these two base-preserving comparisons.

Every finite Galois automorphism extends to an automorphism of the separable
closure by Mathlib's `AlgEquiv.liftNormal`, which retains its value on the
embedded finite field. The two finite-stage comparison equations and the
absolute star-equivariance equation therefore give the desired finite-stage
equation. `CommonFiniteStageStarEquivalence.intertwine_transport` carries out the
root-datum composition calculation by applying the injective target weight
map and cancelling its inverse. Base preservation follows by the same transport
on the root index sets. The result asserts existence of the finite-stage
equivalence; it does not impose an additional chosen recovery equation on it.
