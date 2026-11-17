# Full idelic norms on a fixed finite denominator

This internal module defines `ideleArchimedeanNorm F z` as the supremum
norm of the value of the idele `z` in the published mixed archimedean
space.

If the finite value of `z` is integral at every finite place, its full
idelic absolute value is at most this supremum norm raised to
`[F:ℚ]`. Each infinite completion norm is bounded by its real or complex
mixed coordinate norm. The implemented proof bounds their finite
product using the place multiplicities, whose sum is `[F:ℚ]`. At
finite places, all norm factors are at most one; their finite
multiplicative support allows comparison of the finite product with
one.

More generally, if a nonzero field element `q` clears the finite value
of `z`, then the full norm is at most
`‖arch(q)‖^[F:ℚ] * ideleArchimedeanNorm(z)^[F:ℚ]`.
The proof multiplies `z` by the principal idele of `q`. Its full norm
is one by the published product formula, its finite value is
integral, and its archimedean supremum norm is bounded by the product
of the two supremum norms.

In particular, an idele with integral finite value and mixed
archimedean norm at most one has full absolute value at most one.
These inequalities are intended to absorb fixed nonnegative idelic
root powers into Schwartz rapid decay. No Mellin convergence is
asserted here.
