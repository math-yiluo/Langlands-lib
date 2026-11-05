# Exact normal kernels conditional on Cartier smoothness

`normalKernelRepresentationWithCartier` chooses an actual finite-dimensional
matrix representation of an affine locally finite-type group scheme `G` over
an algebraically closed field `k`. Its full scheme-theoretic kernel has the same
subgroup functor as a specified normal closed subgroup `i : H ⟶ G`. There is no
reducedness, smoothness or characteristic premise on `G`, `H` or `k`. The
construction explicitly takes a proof of the universe-general proposition
`Langlands.GroupScheme.AffineCartierSmoothStatement.{u}` as an additional input.

This is an internal conditional assembly of the existing reduced exact-kernel
construction, the positive-characteristic Frobenius exact-kernel construction,
and smooth reducedness over a field. Its source motivation is Milne,
*Algebraic Groups* (2017), Theorem 3.23 and Lemmas 5.16–5.17, but this module
does not prove Cartier's theorem.

`nonempty_kernelRepresentation_with_cartier` uses the characteristic dichotomy
for a field. In characteristic zero it applies the supplied Cartier proposition
to `G`, deduces that `G` is reduced from its smooth structure morphism, and
invokes `nonempty_kernelRepresentation_of_normal_closed`. In prime positive
characteristic it invokes
`nonempty_kernelRepresentation_of_prime_expChar`, which has no reducedness or
smoothness premise. The two existing constructions both return the actual
`KernelRepresentation i` package. Classical choice selects such a package.

`exists_normal_kernel_with_cartier` exposes the package's natural-number
dimension, its homomorphism to the corresponding general linear group, and its
equality
`SubgroupFunctor.range (kernelι ρ) = SubgroupFunctor.range i`.
That equality is the existing full subgroup-functor equality on every relative
scheme test, including nonreduced tests.

This contribution retains both algebraic closedness and the explicit Cartier
input. It proves no arbitrary-field descent, quotient representability,
flatness or surjectivity. The unrestricted normal quotient existence target
therefore remains a separate obligation.
