# Corank-one quotient unfolding over the real field

This internal comparison implements the change of variables leading to
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.3, p. 58,
(8.3), adapting `ComplexLocalAdjacentUnfolding` to real measure data. Write
`H = GL_(r+1)(ℝ)` and `Q = N_(r+1)(ℝ) \\ H`.
`RealJacquet.RealLocalAdjacentUnfoldingStatement r` takes a pointwise
restriction identity for the supplied upper coefficient `W` on `diag(g,1)`.
It expresses the restriction as a supplied scalar `b` times the integral of
`realAdjacentRestrictionKernel`. The square-matrix test `Φ₁` and the row
test `Φ₂` are arbitrary functions here; in Jacquet's application the latter
is obtained by Fourier transforming the free column. The actual determinant
character `η` absorbs the power of the inducing parameter.

The proof uses invariance of `U(g) V(g z)` under left multiplication by
`N` to evaluate the smaller equal-rank expression at a representative.
In the inner group integral put `k = g z⁻¹`, so that `k⁻¹g = z`.
Invariance under inversion of the supplied real group Haar measure is the
published `realMatrixHaar_symmetries`. The determinant characters of `g`
and `k⁻¹` combine to `η(det z)`. The determinant powers, including the
outer corank-one `s-1/2`, combine to `|det k|^s |det z|^(s+r/2)`.
On `Q × H`, the inverse right-translation shear sends `(N g,z)` to
`(N (g z⁻¹),z)` and preserves the supplied product measure. After this
change, Fubini writes the original ordinary unequal integral as the
integral over `z` of the smaller equal-rank integral for `U` and `V(· z)`,
weighted by the square-matrix zeta kernel. The scalar `b` is retained.

The restricted recursive coefficient identity, unipotent invariance of the
product and absolute integrability of the unfolded joint kernel are explicit
premises. No equality of continuous and uniform coefficient models is used.
This unit does not supply the recursive restriction identity, an
integrability bound, the dual Fourier comparison, meromorphic continuation,
or the functional equation.
