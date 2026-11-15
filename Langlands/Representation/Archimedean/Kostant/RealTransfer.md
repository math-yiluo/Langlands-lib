# From `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` to the one-block product

* `realGL_bracket_eq`: in `ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ`, the base-changed Lie bracket
  `LieAlgebra.ExtendScalars` (the instance used by `RealWhittakerMaximallyFaithfulStatement`)
  is the ring commutator. On pure tensors, `⁅a ⊗ x, b ⊗ y⁆ = ab ⊗ (xy - yx)`; the general case
  follows by additivity.
* `toGL n : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) ≃ₗ⁅ℂ⁆ GLProd ℂ (fun _ : Unit => n)` is
  `z ⊗ X ↦ z X`, built from Mathlib's `matrixEquivTensor`. It is `ℂ`-linear
  (`matrixEquivTensor_symm_smul`) and respects brackets by `realGL_bracket_eq`.
* `isWhittaker_comp`: suppose `ℓ(π(1 ⊗ X) v) = (i ∑_p a_p X_{p,p+1}) ℓ(v)` for real strictly
  upper triangular `X`; this is the condition of `IsRealGenericGKModule`. Then `ℓ` satisfies
  `IsWhittaker` for `π ∘ toGL⁻¹` with coefficients `i a_p`. A complex strictly upper triangular
  matrix `X` equals `toGL(1 ⊗ Re X + i ⊗ Im X)`, and `π(i ⊗ Y) = i π(1 ⊗ Y)`, so the
  character values add up to `∑_p i a_p X_{p,p+1}`.

These are the coefficients `η(E_{p,p+1}) = i a_p` described in item 2 of
`RealGenericLargeReduction.md`, up to Kostant's dual sign convention.
