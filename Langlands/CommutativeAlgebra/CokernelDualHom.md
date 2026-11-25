# The module representing the kernel of a map of finite projective modules

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.CommutativeAlgebra.CokernelDualHom`. Let `δ : K₀ → K₁` be a map of finite
projective modules over a commutative ring `A`.

- `tensorEquivHom B K : B ⊗_A K ≃ₗ[A] (K^∨ →ₗ[A] B)`, `b ⊗ k ↦ (φ ↦ φ(k) • b)`, for an `A`-algebra
  `B` and finite projective `K` (Mathlib's `dualTensorHomEquiv` and `Module.evalEquiv`).
- `Q δ := K₀^∨ ⧸ δ^∨(K₁^∨)`.
- `homEquiv δ B : (Q δ →ₗ[A] B) ≃ {x : B ⊗ K₀ // (1 ⊗ δ) x = 0}`, the defining property of `Q`.
- `homEquiv_comp` (naturality in `B` along algebra maps) and `homEquiv_smul` (linearity over
  `B`), with the auxiliary `tensorEquivHom_naturality`, `tensorEquivHom_rTensor` and
  `tensorEquivHom_smul`.

## Source

This is the construction of Kleiman, *The Picard scheme* (arXiv math/0504020v1), Subsection 3.10
(p.24): for a complex `K⁰ → K¹` of locally free modules computing `f_*(F ⊗ f^*N)` in degree zero,
`Q = Coker(K¹^∨ → K⁰^∨)` satisfies `Hom(Q, N) ≅ Ker(K⁰ ⊗ N → K¹ ⊗ N)` (3.10.1). Here it is stated
for `N = B` an `A`-algebra, which is the case used for the linear system.
