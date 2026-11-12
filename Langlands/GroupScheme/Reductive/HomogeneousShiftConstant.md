# A homogeneous polynomial constant along a line forces a constant parameter

Author: Worker 1502. Internal helper for the proof of
`AffineHomogeneousQuotientReductiveStatement`. It is elementary commutative algebra and does not
follow a cited source.

Namespace `Langlands.GroupScheme.HomogeneousShift`. `K` is a field.

- `aeval_smul_of_isHomogeneous`: if `F : MvPolynomial σ K` is homogeneous of degree `d`, then for
  every commutative `K`-algebra `S`, `t : S` and `x : σ → S`,
  `aeval (t • x) F = t ^ d * aeval x F`. The proof expands `F` as a sum of monomials and uses that
  each monomial in the support has total degree `d`.
- `mem_range_of_isIntegral`: if `K` is algebraically closed and `x` is an element of a domain `C`
  that is integral over `K`, then `x` is the image of a scalar. The minimal polynomial of `x` is
  irreducible over `K`, hence of degree one, and its root is `x`. This follows the proof of
  Mathlib's `IsAlgClosed.algebraMap_bijective_of_isIntegral`, applied to a single element.
- `mem_range_of_aeval_shift`: let `K` be algebraically closed, `C` a `K`-algebra that is a domain,
  `F` homogeneous of degree `d > 0`, and `w a : σ → K` with `F(a) ≠ 0`. If
  `F(w + ψ a) = c` in `C` for some `ψ : C` and `c : K`, then `ψ` is the image of a scalar.

## Proof of `mem_range_of_aeval_shift`

Put `r(X) = F(w + X a) - c ∈ K[X]`; then `r(ψ) = 0`. The polynomial `r` is nonzero. Otherwise
`F(w + t a) = c` for every `t ∈ K`, and by homogeneity
`F(t w + a) = t^d F(w + t⁻¹ a) = c t^d` for every `t ≠ 0`. The polynomial
`p(X) = F(X w + a) - c X^d` would then have infinitely many roots (`K` is infinite), so it is zero.
This contradicts `p(0) = F(a) ≠ 0`, which holds because `d > 0`. Hence `ψ` is algebraic, and so
integral over the field `K`, and `mem_range_of_isIntegral` applies.
