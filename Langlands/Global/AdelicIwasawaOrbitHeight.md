# Iwasawa character values and rational projective orbit heights

For an actual finite matrix representation and a nonzero rational vector,
`rationalOrbitPoint` takes the projective class of the transformed vector.
The local supremum norms of the principal vector agree with the coordinate
absolute-value suprema in Mathlib's multiplicative height. The finite-place
bijection and archimedean multiplicities give equality of the full products.

If the rational vector is a parabolic eigenvector on the adeles, the
factorization `x = p(q) k` computes its inverse orbit height at `x⁻¹`.
The right parabolic factor multiplies that height by the inverse normalized
character norm, which is `exp (-H_P(x)(χ))`. For rational `x` the left side
is the projective height of the rational inverse orbit point. Compactness
bounds the height of `k⁻¹`, giving a uniform upper bound on `H_P(x)(χ)`
minus the corresponding logarithmic decay.

This internal calculation uses the published Iwasawa factorization and the
primitive adelic height scaling law. It relates arithmetic projective
heights to the parameter estimates for Mœglin–Waldspurger II.1.5.
