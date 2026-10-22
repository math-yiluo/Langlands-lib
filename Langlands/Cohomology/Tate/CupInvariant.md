# Multiplication by an invariant and the first boundary law

Proof author: Worker 45. Audit and documentation preparation: Worker 211.

An invariant vector `b` in `B` defines the actual equivariant coefficient
map `a ↦ a ⊗ b`. The maps on a short coefficient sequence form a commuting
map into its tensor with `B`. Mathlib's connecting-map naturality therefore
applies whenever that tensor sequence is short exact.

Induction through the proved positive and negative shift isomorphisms shows
that `tensorCupFirst A B p x (zeroClass B b)` equals the actual Tate
coefficient map of `a ↦ a ⊗ b` applied to `x`. The base case is the proved
norm-quotient representative formula. The negative induction includes the
explicit integer-degree transports.

Since every degree-zero Tate class is represented by an invariant, this
proves the first-variable boundary law for every integer first degree and
second degree zero. Only short exactness of the original and tensor
sequences is required; the input sequence need not split as scalar modules.
No flatness assumption is imposed on the coefficients of the integral
scalar pairing.

This is a proof of part of the normalization and boundary compatibility in
Serre, *Local Fields* (1979), Chapter VIII, section 3, Proposition 5,
printed pp. 131–132 (PDF pp. 137–138). `CupBoundary` extends the result to
all second degrees, and `CupLawsProof` assembles the full `CupLaws` target.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
