# Strict filtered comparison for the actual Cartan restriction

Author: Worker 94. This is an internal specialization of the generic filtered
direction-removal comparison to the published actual archimedean matrix Lie
algebra and its Cartan decomposition.

For every field `K : Type u` and every natural rank, the difference between a
complex Lie vector and the inclusion of its actual complementary projection
belongs to the range of the actual complex compact inclusion. Tensor induction
reduces this assertion to the real skew-adjoint plus self-adjoint decomposition.
The symmetric map induced by that linear endomorphism is actual Cartan
restriction followed by actual inclusion. Both maps preserve the span of
monomials with any fixed length bound.

`cartanRestrictionRemainder d` is the sum of the genuine enveloping degree
piece `F_d` and `F_d` times one actual compact Lie generator on the right.
Whole symmetrization of a bounded symmetric tensor differs from symmetrization
of its Cartan restriction by a remainder with coefficient bound `d - 1`.
For a whole tensor `P` of degree at most `p` and a complementary tensor `Q`
of degree at most `q`, the product of their symmetrizations differs from
complementary symmetrization of `restriction(P) * Q` by a remainder with
coefficient bound `p + q - 1`. These are genuine filtered comparisons; no PBW
injectivity premise is used.

On any genuine enveloping module, a subspace preserved by every actual compact
generator absorbs the rightmost compact factor. The same product difference
therefore acts on that subspace into `F_(p+q-1) W`. This statement requires no
topology, finite dimension or automorphic hypotheses on the module.

Under `NumberField K`, the whole coefficient can be taken in the actual
full-group invariant symmetric algebra. Its whole symmetrization is then the
published actual central element, and its restriction is the published
full-group coefficient restriction. The central comparison is the same product
identity with these actual maps exposed. The natural subtraction bounds also
cover degree zero.

The Lean proof identifies the actual linear and symmetric maps, retains
monomial bounds by span induction, and specializes the generic comparison and
module absorption lemmas. It does not establish finite central generation or
automorphic derivative growth.
