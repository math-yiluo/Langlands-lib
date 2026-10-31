# Absolute convergence of the actual rank-one-pair block integrals

Worker 396. Internal derived prerequisite for the matrix functional-equation
comparison. The field and representation-carrier universes remain independent,
and the original representation may be reducible of full Whittaker type.

`RankOneBlockConvergence.integrable_quotient_prod_iff` transports absolute
integrability on the product of the actual rank-one quotient and any supplied
s-finite measure space to the product of `GL1` and that space. It uses the
actual quotient homeomorphism, the definition of `rankOneQuotientHaar` as a
pushforward of normalized group Haar, and the product of measurable equivalences.
No scalar measure factor is introduced.

`converges_of_finite_expansion` assumes an exact pointwise expansion of one
block coefficient in the form

```text
W(M(g,X)) = sum_i phi_i(X) * Wi(appendIdentity(g)),
```

where every `Wi` belongs to the same original coefficient image and every
`phi_i` is an actual rectangular Schwartz–Bruhat function. If all diagonal
model restrictions with their determinant weight are integrable at `s`,
each weighted summand is integrable on the product: its group factor is
one of those diagonal restrictions and its rectangular factor is continuous
with compact support. The finite sum equals the actual block integrand
with the canonical constant-one second model vector. This proves absolute
product convergence, rather than merely an identity of scalar integrals.

`converges_of_diagonal_integrable` discharges the expansion premise under
full Whittaker type and nonvanishing of the specified first functional.
The published `unequalRankCompactSupport` supplies uniform compact support
in all rectangular variables. The published `unequalRankFiniteExpansion`
then produces the exact expansion using vectors of that same coefficient
model. No analytic continuation or convergence is assumed in that expansion.

`AllBlocksConvergeOnRight` is a Prop-valued assertion: for every allowed
block `(j,k)`, one right half-plane works for every first model vector with
the canonical second vector, at the specified quotient measure. The bound
may depend on the block but is chosen before all first vectors.

`convergesOnRight_of_matrix` proves this convergence for a specified block
at `rankOneQuotientHaar`. The published BoxConvergence theorem first supplies
a common half-plane for every actual rank-one model integral. At smaller
rank one, `appendIdentity 0 (j+k+1) g` is explicitly proved to be the actual
rank-one determinant diagonal; its determinant exponent is checked to be
`s-(j+k+1)/2`. Thus the same bound works for all diagonal restrictions, and
the finite-expansion argument gives absolute convergence of every first
vector in this block. The rank equality is transported by the actual
`whittakerRankCast`, retaining the original functions.

`allBlocksConvergeOnRight_of_matrix` extends this to every compatible
rank-one quotient measure using the published uniqueness theorem. Its
only analytic input is the actual common matrix convergence of the specified
coefficient-model representation. The same supplied additive Haar measure
`nu` supplies every rectangular product measure.

`dualBlockZero_convergesOnRight_of_iota` applies the result to the constructed
first-dual coefficient model. The supplied inverse-transpose matrix analytic
assertions give its ordinary matrix assertions via DualConvergence; full
Whittaker type and nonzero functional transfer through the published actual
dual construction. Applying the block result at `(r-0-1,0)` yields one bound
before all original first vectors. The first function is exactly the
rank-cast right translate of `firstDualFunction` by `blockWeylAt 0 r hrpos`,
and the second is exactly the second dual of `rankOneTrivialModelOne`.
The latter is proved equal to the actual canonical constant-one vector for
`psi.scale(-1)`. Hence the conclusion is absolute product convergence of
the genuine complementary-block dual integrand on a right half-plane.

This strengthens the separately submitted scalar ComplementaryContinuation
argument: scalar equality alone is not used to infer absolute convergence.
The proof uses an exact finite pointwise expansion and integrability of each
separable summand. No new original-source transcription, irreducibility,
finite length, multiplicativity or conditional I1/I2/I3 comparison is used.
The paired normalized functional equation and final all-rank gamma comparison
remain later obligations.
