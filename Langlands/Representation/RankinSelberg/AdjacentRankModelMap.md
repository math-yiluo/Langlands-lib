# The linear adjacent-rank integral map

This internal, derived module packages the published literal JPSS Section 6.1
integral as a complex linear map from the entire algebraic test tensor product
to functions on the ambient general linear group. It retains the original
coefficient image, the supplied additive character, Haar measure and self-duality
certificate, and the arbitrary continuous multiplicative character.

The only analytic input is the published
`adjacentRankModelConverges_tmul_of_isSmooth` from
`AdjacentRankModelConvergenceProof`. That theorem proves absolute convergence
of the literal pure-tensor integrand for every character and ambient element.
Tensor induction and additivity of integrable functions extend it to every
finite tensor using only smoothness of the original representation.
`Padic.adjacentRankModelMap` then uses the existing integral additivity and
scalar laws. No topology or norm on the original representation or its
coefficient image is chosen.

`Padic.adjacentRankModelMap_exists_sum_tmul` is an equality of entire functions:
one finite list of tests works at all ambient elements.
`Padic.range_adjacentRankModelMap` identifies the linear range with the complex
span of pure-tensor images. It uses this finite decomposition for one inclusion
and the submodule property of a linear range for the other.

`adjacentRankFourierEquiv` tensors the actual supplied last-column partial
Fourier equivalence with the identity on the coefficient image. Its intertwining
formula follows from the published Schwartz-factor Fourier conjugacy, first on
pure tensors and then by tensor induction.
`Padic.range_adjacentRankModelMap_fourier` uses its surjectivity to preserve the
whole function range. `Padic.adjacentRankModelIntegral_mul` proves the exact
right-translation formula, including the specified outer character and
determinant power, from the representation law for `rho0` and multiplicativity
of these scalar factors.

These are algebraic consequences of the published model and its convergence,
motivated by the tensor and partial Fourier steps of JPSS,
*Rankin–Selberg Convolutions* (1983), Section 6.1, printed pages 428–431.
They neither construct induced sections nor assert their spanning, convergence
of the Jacquet double integral, existence of an induced Whittaker functional,
or the adjacent-rank image-equality theorem.

The canonical p-adic helper instances have explicit module-specific names so
this module can be imported with `AdjacentRankStarData`. Their types, bodies
and local instance scope are unchanged.
