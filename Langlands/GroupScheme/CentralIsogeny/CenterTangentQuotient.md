# Central isogenies with exact centre-tangent kernel

Author: Worker 1487.

This internal deduction combines the actual finite central Frobenius subgroup
with its finite central quotient. In positive exponential characteristic
`p > 1`, every smooth affine group G over an arbitrary field k admits a
central isogeny `q : G ⟶ Q` onto a smooth affine group such that, on every
commutative k-algebra A, the kernel of the actual linear differential of q
equals the tangent submodule of the full scheme-theoretic centre of G.
The statement includes the zero algebra. Neither the centre nor the finite
kernel is required to be smooth.

`lie_range_kernelι_eq_ker_targetMapLinear` first proves a general identity:
the actual tangent submodule of the range of the scheme-theoretic kernel
inclusion is the kernel of the actual linear target map. The proof applies
the all-test kernel membership criterion to a dual-number identity point.
Equality to the zero additive tangent vector is exactly equality of its
underlying multiplicative point to the identity.

`exists_centralIsogeny_ker_targetMapLinear_eq_center_lie` chooses the finite
central normal closed subgroup constructed in `CentralFrobeniusKernel`.
Its tangent submodule is the centre tangent submodule on every algebra.
The finite central subgroup quotient gives a smooth affine target and a
central isogeny with exactly this subgroup as its kernel functor. Substituting
the kernel range equality in the general tangent identity proves the result.

`exists_connected_centralIsogeny_ker_targetMapLinear_eq_center_lie` also
retains connectedness when G is connected: the underlying quotient map is
surjective and continuous, so its image is connected.
`CenterTangentQuotientStatement.{u}` packages this connected assertion and
`centerTangentQuotient` proves it.

This result is derived from the existing actual kernel, subgroup tangent,
finite central Frobenius subgroup, and finite central quotient constructions.
It does not prove that the quotient has no nonzero central semisimple tangent
vectors, that repeated quotients terminate, that geometric weights decrease,
or that target tori lift. Those structural assertions and the parent no-torus
theorem remain separate obligations.
