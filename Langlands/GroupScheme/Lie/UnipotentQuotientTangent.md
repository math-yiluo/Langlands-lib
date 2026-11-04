# Semisimple tangent lifts through unipotent quotients

The construction `Lie.unipotentQuotientTangentFactor` takes a monomorphic
inclusion `i : N → G` whose all-test range is exactly the full scheme kernel
of `q : G → Q`. The target `Q` is affine and locally of finite type and is
unipotent. Given the explicit input `UnipotentSemisimpleStatement` and an
actual semisimple tangent vector `X` of `G`, it constructs a tangent vector
of `N` mapping to `X`. The reconstruction equality is proved. The base field
and its universe are arbitrary; neither the group nor the kernel has to be
smooth for this construction.

The proof maps semisimplicity along the actual group-scheme homomorphism `q`.
The vanishing input makes the image tangent vector the identity. Equality of
the full all-test kernels then lifts the actual dual-number point through
`i`. Monicity of `i` reflects reduction to the identity, so the lift is an
actual tangent vector. This uses no surjectivity on rational points or on
test-algebra point groups.

The fppf-quotient corollary assumes smoothness of `G`; the published descent
theorem makes `Q` smooth and hence locally of finite type. It therefore needs
no separate finiteness assumption on `Q`. A second corollary combines this
with the explicit `NilpotentCentralTorusStatement`: one central maximal torus
of a smooth connected affine nilpotent group contains every semisimple
actual tangent vector. That torus is chosen before the vector, so the
conclusion is uniform in the vector.

These are derived adapters for the quotient step of Milne, *Algebraic Groups*
(2017), Proposition 17.90, printed p.381 / PDF p.397, using the structural
central-torus input of 16.47 and unipotent vanishing derived from Example
17.75. Both structural statements remain explicit assumptions in the Lean
results. No proof of those inputs, of containment in an arbitrary chosen
maximal torus, or of the Cartan generation theorem is claimed here.
