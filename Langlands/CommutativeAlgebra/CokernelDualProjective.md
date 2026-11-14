# Projectivity of `Q` from exactness on fibres

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.CommutativeAlgebra.CokernelDualHom`.

- `projective_Q_of_projective_coker`: if `K₁ ⧸ δ(K₀)` is projective, then `Q δ` is projective.
  The image of `δ` is then a direct summand of `K₁`, hence projective, so `δ : K₀ → δ(K₀)` has a
  section `s`; `φ ↦ φ ∘ s ∘ δ` is an idempotent of `K₀^∨` with image `δ^∨(K₁^∨)`, which makes `Q`
  a direct summand of the projective `K₀^∨`.
- `projective_of_lTensor_field_injective`: over a local ring `B`, a finite module `C` with a map
  `u` to a finite free module such that `k ⊗ u` is injective for some field `k` over `B` with
  kernel the maximal ideal is projective. Injectivity descends to the residue field (a field
  extension is faithfully flat), and Mathlib's
  `IsLocalRing.split_injective_iff_lTensor_residueField_injective` splits `u`.
- `lTensor_liftQ_injective`, `projective_coker_of_exact`: for `K₀ →δ₀ K₁ →δ₁ K₂` with
  `δ₁ ∘ δ₀ = 0` over a noetherian ring, if for every maximal ideal `P` there is a field `k` over
  `A` with kernel `P` such that `k ⊗ K₀ → k ⊗ K₁ → k ⊗ K₂` is exact at `k ⊗ K₁`, then
  `K₁ ⧸ δ₀(K₀)` is projective (Mathlib's `Module.projective_of_localization_maximal'`, applied to
  the localizations `A_P ⊗ (K₁ ⧸ δ₀ K₀)`, with the map induced by `δ₁`).
- `projective_Q_of_exact`: under the same hypothesis, `Q δ₀` is projective.

## Source

Kleiman, *The Picard scheme* (arXiv math/0504020v1), Subsection 3.10, p.25: condition (v)
(`H¹(X_s, F_s) = 0`) implies (i) (`Q` is free near `s`). For the step (v) ⇒ (ii), Kleiman cites EGA III₂ 7.5.3 or
Ogus–Bergman [OB72], Corollary 2.1, p.68. This file proves the commutative-algebra step in the form used
here: exactness of the Čech model at `K₁` on every closed fibre makes `Q` projective.
