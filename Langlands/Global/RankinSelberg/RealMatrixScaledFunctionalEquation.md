# Real square matrix functional equation at a nonzero Fourier parameter

**Provenance.** This is the change-of-character form of the matrix zeta equation of Hervé Jacquet, *Archimedean Rankin–Selberg integrals* (2009), (4.3) and Proposition 4.4 in §4.7, pp. 30–31. The parameter `b` here gives the positive-sign phase `exp(2π i b tr(XᵀY))` in the self-dual measure. To compare to Jacquet's negative phase with input additive parameter `a`, use `b = -a`.

Take rank `n = r + 1`, a Haar measure on `GL_n(ℝ)` and a sigma-finite Haar measure on `O(n)`. For a smooth section `f` of the position principal series and a linear form `ℓ` with the compact derivative bound, set `F(g) = ℓ(translate g f)`. For `b ∈ ℝˣ` and a square Schwartz matrix test `Φ`, `RealMatrixCompactFunctionalEquationStatement` gives absolute convergence and holomorphy on a common right half-plane and meromorphic continuations `M, Md` for the normalized zeta integrals of `(F, Φ)` and `(F ∘ inverseTranspose, matrixTransform b Φ)`. Their codiscrete relation is `L(s) Md(1−s) = E_b(s) Ld(1−s) M(s)`, with `L = torusL e u`, `Ld = torusL e (−u)` and

`E_b(s) = torusEpsilon e * (∏ᵢ χᵢ(b)) * |b|^(n(s−1/2))`.

The products use the position characters `χᵢ`; the result is for these coefficients and factors, not for an arbitrary Langlands quotient. No all-pair theta identity, normalized-entire assertion or vertical-strip bound is claimed.

**Lean proof.** In Euclidean matrix coordinates the Fourier transform changes by the scalar `|b|^(n²/2)` and argument multiplication by `b`. A scalar matrix commutes with the source group action. Its normalized Borel half-modulus is one because reversal negates the diagonal half-modulus exponents, so the coefficient gains `∏ᵢ χᵢ(b)` when translated by the scalar matrix. In the dual integral make the left-Haar change of variables by the inverse scalar matrix. This uses the genuine inverse transpose and determinant shift. The resulting multiplier on the standard-character dual integral at `s` is `∏ᵢ χᵢ(b) * |b|^(n(1/2−s))`, an entire function of `s`. Multiply the standard-character dual continuation by this factor and use the same factor at `1−s` in the functional equation. Integrability and initial holomorphy transfer along the same change of variables and multiplier.

**Public helper results.** The proof steps above are also stated as public lemmas, which
`RealMatrixNormalizedGrowth` reuses:

- `realMatrixFunctionalCoefficient_dual_scalar`: translating the inverse-transpose coefficient
  `g ↦ ℓ(translate (ιg g) f)` by the inverse scalar matrix multiplies it by `∏ᵢ χᵢ(b)`.
- `realMatrixScaledDualFactor b ω s = ω · |b|^(n(1/2 − s))` is entire
  (`differentiable_realMatrixScaledDualFactor`).
- `realMatrixZetaKernel_scaled_dual` and `realMatrixZeta_scaled_dual`: if a dual coefficient
  `fd` satisfies `fd((b·1)⁻¹ g) = ω · fd(g)`, then at every `s`
  `realMatrixZeta μ fd (matrixTransform b Φ) s = realMatrixScaledDualFactor b ω s · realMatrixZeta μ fd (matrixTransform 1 Φ) s`.
  The proof uses left invariance of the Haar measure under the inverse scalar matrix
  (`integral_mul_left_eq_self`) and the kernel identity. The integral identity holds at every
  `s`, whether or not the integrals converge, because both sides are Bochner integrals related
  by a measure-preserving change of variables and a constant factor.
