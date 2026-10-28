# Scalar coefficients of pure-tensor cell sections

`TwoBlockCellCoefficientStatement` is an internal intermediate assertion for the
JPSS two-block extension construction. For smooth factor representations, any
standard Whittaker functionals, any rectangular additive Haar measure, any
rectangular Schwartz–Bruhat function `Ψ`, and any pair of factor vectors, it
asserts existence of an actual coefficient in the intrinsic Whittaker set of
the canonical ordered normalized induction.

At the exchanged leading embedding of `g ∈ GL_B`, where `A=a+1` and `B=b+1`,
the coefficient equals the positive half modulus at the original-order Levi
element `diag(I_A,g)`, times `ℓ₁(v₁) ℓ₂(π₂(g)v₂)`, times
`∫ ψ(-x_(B,1)) Ψ(g⁻¹x) dx`. The topology and Borel structure are canonical.
The functionals and vectors may be zero; irreducibility and multiplicity one
are not required. The coefficient belongs to an actual coefficient image,
rather than merely satisfying a transformation law.

The assertion is derived from three existing ingredients. Section existence
realizes `Ψ(x) (v₁⊗v₂)` on the actual cell submodule. The ambient functional
extension agrees there with the scalar Jacquet integral. Leading-block
translation preserves this submodule and gives the normalized tensor action
on `Ψ(g⁻¹x) (v₁⊗v₂)`. Contracting the pure tensor and taking constants out of
the scalar integral gives the displayed formula. This derivation uses no
Fourier surjectivity assumption or prescribed-value extension result.

This file states the proposition. It does not prove it or replace the host
extension formula: Fourier realization, determinant-power simplification,
and the independently lifted carrier universes remain separate steps.
