# Lifting points of affine smooth schemes over complete rings

This internal prerequisite uses actual morphisms in `Over (Spec R)`, through the
published `PointTopology.RingPoint` carrier. It proves that for an affine scheme
`X` smooth over a commutative ring `R`, an `R`-algebra `S` complete for an ideal
`I` has a surjective point reduction map from `X(S)` to `X(S / I)`. The reduction
is the existing change of coefficient ring by the literal quotient algebra map.
The construction `adicPointLift` chooses an actual lift of any specified
quotient-valued point. Its theorem `adicPointLift_changeRing` proves that
reduction gives exactly that point. The construction allows arbitrary ideals
and requires adic completeness, rather than only completeness for an unrelated
topology. It is noncomputable and asserts no canonical choice or naturality of
the chosen lift.

The proof identifies actual points with algebra maps out of the canonical ring
of global sections. Smoothness of the structure map implies smoothness of this
coordinate algebra. Mathlib's
`Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` then supplies a lift
of each quotient-valued algebra map with the prescribed reduction. The proved
change-of-ring formula from `PointTopology/AffineProductRingTopologyProof` carries that equality back to actual scheme morphisms.
In particular, a point modulo an ideal of an adically complete base gives an
actual base-valued point.

This is a derived complete-ring version of the smooth lifting step used in
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Lemma B.2.4
and the proof of Theorem B.2.5, printed pp.543–544 / PDF pp.548–549. The registered
October 2026 errata has no correction to this passage. The implementation uses
adic formal smoothness directly; it does not claim the general Henselian-ring
version, torsor triviality, existence of good arithmetic models, parabolic
covering, or maximality of integral-point groups.
