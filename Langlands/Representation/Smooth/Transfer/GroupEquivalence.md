# Algebraic dual and smooth-vector transport

This module contains the shared pullback identities used by compact-coefficient
classes and Godement–Jacquet coefficient transport. The declarations retain their
original names, statements and proofs from `CompactCoefficient.GroupTransport`.
They concern complex representations on arbitrary additive carriers, with
independent group and carrier universes. The groups need only group and topology
instances; continuous multiplication and inversion are not assumed.

The declarations in this paragraph are in namespace `Langlands`.
`dual_comp_monoidHom` identifies the actual algebraic dual of a pulled-back action
with the pullback of its algebraic dual. It evaluates a functional on a vector
and uses preservation of inverse by the group homomorphism. Thus the identity is
valid even for infinite-dimensional carriers, without replacing the algebraic
dual by a finite-dimensional model.

`isSmoothVector_comp_continuousMulEquiv_iff` proves equivalence of smooth-vector
conditions by applying the published `isSmoothVector_comp` in both directions.
For the reverse implication, the pullback by `e.symm` has exactly the original
action because `e (e.symm g) = g`.
`isSmoothVector_dual_comp_continuousMulEquiv_iff` applies this equivalence after
rewriting by `dual_comp_monoidHom`. In particular, a functional that is smooth
for the pulled-back dual is smooth for the original dual, and conversely.

The dual identity applies to every group homomorphism, without topology
hypotheses. The two smoothness equivalences require a continuous multiplicative
equivalence. They impose no admissibility, finite-dimensionality or smoothness
hypothesis on the whole representation. Their internal proofs use the published
`Smooth.Transfer.PullbackProof` and actual algebraic dual action, and assert no
additional result from the literature.
