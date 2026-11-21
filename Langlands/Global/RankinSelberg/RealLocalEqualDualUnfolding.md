# Real equal-rank dual unfolding of a Godement quotient coefficient

**Source.** Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), Proposition 7.3 and §8.2, pp. 55–56, equation (8.1) and the first dual integral on p. 56. This is the internal joint-integrability form of the latter identity, at an arbitrary dual spectral argument `s` in place of the source’s `1 − s`. It uses the actual Godement quotient kernel and the same explicit Haar comparison as the primal unfolding.

## Statement

Let `m = t + 1`, `n = t + 2`, and let `D` and `D'` be compatible real quotient data at matrix sizes `m` and `n`. Fix a nonzero real additive parameter `b`, a rectangular Schwartz test `Φ`, a last-row function `φ`, real character data `d`, and two functions `W` and `V` on the smaller and larger groups satisfying `KernelWhittakerLaw b W` and `KernelWhittakerLaw (-b) V`. Thus the smaller function transforms for the parameter `-b`, and the larger one for `b`. Write `R` for `equalRecursiveCoefficient b D Φ W hW d` and `C_d = d(-1)^m` for its constant normalization, with `d` evaluated via its character.

`RealLocalEqualDualUnfoldingStatement` assumes that `D'.unipotentHaar` is a positive scale `c` times `upperStepHaar (t+1) b`. It also assumes joint integrability, at `s`, of `equalUnfoldedKernel` with `d.inverse`, the duals of `W` and `V`, and the product of the two Fourier tests: `realRectangularSchwartzFourier b Φ` on the first `m` rows and `realFourierTransform b φ` on the last row. The measure is the product of the lower quotient measure and the larger group Haar. The conclusion is that the actual dual equal-rank integrand for `R`, `V` and `φ` is integrable on the larger quotient and that

\[
 c\,\mathrm{realEqualDualIntegral}_{b,D'}(R,V,\phi;s)
    = C_d\int J_{\mathrm{dual}}(q,g)\,d(D\!\operatorname{.measure})(q)\,d(D'\!\operatorname{.groupHaar})(g).
\]

Both Fourier transforms use the same `b`. In the convention of `RealLocalUniformPositiveEqualContinuationStatement`, set `b = -a`.

## Implemented proof

1. For the dual of `R` at `g`, the Godement kernel is evaluated at `w_n w_n g^ι = g^ι`, where `g^ι` denotes the inverse transpose. Apply `realGodementQuotientReflection` with input `w_n g`. Inverse transpose fixes `w_n`, so the reflected input of that theorem is also `g^ι`. The resulting kernel has additive parameter `-b`, the rectangular Fourier test at `b`, the lower dual coefficient, inverse character data, and input `w_n g`. The reflection scalar is `d((-1)^m) = C_d`. Inversion of `d` does not change its value at `-1` since `(-1)⁻¹ = -1`. Thus the new kernel's recursive normalization is again `C_d`, giving the pointwise formula `R̃ = C_d · R'` for the normalized reflected recursion `R'`. This step is an identity of the total Bochner integrals in quotient reflection; it does not need the joint-integrability premise.
2. Apply `realLocalEqualUnfolding` at `-b` to `R'`, the dual of `V`, and the two Fourier tests. The reflected laws are supplied by `KernelWhittakerLaw.dual`. The quotient Haar comparison has the same scale by `upperStepHaar_neg`. The result gives integrability of the reflected recursion's equal integrand and equates its scaled integral with the joint integral. Pointwise substitution of `R̃ = C_d · R'` makes the actual dual integrand a constant multiple of that integrable function. Pull the constant through the integral to obtain the equation.

## Scope

The pair proves the reflected Fubini step conditional on the dual joint integral being integrable. It does not establish that premise on a right half-plane, identify the Fourier product with the square-matrix transform, supply a matched finite sum, or identify the recursion with a spanning family of the uniform model. It does not prove `RealLocalUniformPositiveEqualContinuationStatement`.
