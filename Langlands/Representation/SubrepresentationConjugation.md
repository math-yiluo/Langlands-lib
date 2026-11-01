# Invariant subspaces under a covariant linear equivalence

Author: Worker 2. The Integrator extracted the identical helper from
`OperatorDeterminantTwist` and `OperatorCMTransport` without changing its
type or construction.

For complex representations `ρ` and `τ`, a monoid automorphism `α`, and a
linear equivalence `e` satisfying `τ(a)(e(v)) = e(ρ(α(a))(v))`,
`Langlands.conjugatedSubrepresentationOrderIso` identifies their invariant
subspaces. The forward map is linear image, the inverse is linear preimage,
and the order and inverse laws reuse `Submodule.orderIsoMapComap`.

The two automorphic modules reuse this common construction with their
respective covariance formulas. No new mathematical assertion is introduced.
