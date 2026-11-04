# Prescribed maximal tori and semisimple tangent vectors

Over an arbitrary field `k : Type u`, the construction
`torusUnipotentKernelFactor` factors a homomorphism from any actual torus
through a monomorphic subgroup inclusion `i : N → G` whose all-test range
is the full scheme kernel of `q : G → Q`. The target `Q` is affine and
unipotent. Neither smoothness nor finite type of these three group schemes
is required for this construction. The torus need not be split.

The published theorem that every homomorphism from a torus to an affine
unipotent group is trivial kills the composite to `Q`. Thus every
test-scheme point of the torus maps into the full kernel. The represented
range of `i` then supplies a canonical group-scheme factor. The companion
theorem proves that this factor composed with `i` is the original map.

When `N` is a commutative torus, `i` is closed, and the original torus map
is maximal in `G`, the factor is an isomorphism by the published definition
of maximality. This compares actual subgroup schemes; it assumes neither
conjugacy of maximal tori nor surjectivity on rational points.

The final theorem `Lie.exists_tangent_lift_of_nilpotent_maximalTorus`
assumes the exact propositions `NilpotentCentralTorusStatement` and
`UnipotentSemisimpleStatement`. For a smooth connected affine group with
the published geometric nilpotence predicate, any prescribed maximal torus
then contains every semisimple actual tangent vector. The central-torus
input supplies a closed torus kernel and an affine unipotent fppf quotient.
The quotient tangent adapter lifts the given vector into that kernel.
The comparison isomorphism carries the lift into the prescribed torus,
and its inverse identity proves reconstruction of the original vector.

These are derived adapters for the nilpotent quotient step of Milne,
*Algebraic Groups* (2017), Proposition 17.90, printed p.381 / PDF p.397.
The factorization route also follows the proof of Theorem 16.47(a), printed
p.341 / PDF p.357, where maps from multiplicative-type groups to unipotent
groups are killed using Corollary 14.18. Here only torus sources are needed,
and the existing nonsplit-torus theorem is reused. The two structural
propositions remain explicit assumptions. This module proves neither
those propositions nor the full Cartan generation statement.
