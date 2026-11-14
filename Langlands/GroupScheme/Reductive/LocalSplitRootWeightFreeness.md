# Root weight modules over a local ring

`localRootWeightSpaceEquiv` chooses a linear isomorphism from each actual
root exponent weight module to the original local ring.
`localRootWeightSpace_nonempty_linearEquiv` proves the existence needed
by this construction.
The hypotheses are a reductive group over the spectrum of an arbitrary
commutative local ring, a coordinate split torus maximal on every residue
fibre, and a fibrewise root datum on the coordinate lattices. There is no
reducedness, noetherian, henselian or characteristic hypothesis.

The implemented proof uses the finite projective weight summands of
`RelativeAdjointWeightRanks`, through the underlying-ring instances in
`GeometricAdjointWeightRanks`. Mathlib's local-ring finite-flat freeness
theorem makes the original summand free. The actual group over the residue
field is connected reductive by `IsReductive.isConnectedReductive_baseChange`,
and the actual canonical coordinate torus is maximal there by
`splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`.
`IsFibrewiseRootDatumOf.mem_roots_iff` identifies the supplied root as an
actual field-fibre root. The published `splitRootLieLine` theorem gives its
dimension one. The actual weight base-change equivalence and invariance of
the rank of a free module under scalar extension imply rank one over the
original ring, hence the required linear equivalence.

This is an internal consequence of the cited published module interfaces
and Mathlib's local-module theorems. Its mathematical purpose is the local
case of the free-root-space condition in Brian Conrad, *Reductive group
schemes* (2014), Definition 5.1.1, pp.136–138. That condition allows the
local isomorphism target to be obtained from the affine Isomorphism Theorem
(Theorem 6.1.17, p.197), once a proof of that theorem is available.
