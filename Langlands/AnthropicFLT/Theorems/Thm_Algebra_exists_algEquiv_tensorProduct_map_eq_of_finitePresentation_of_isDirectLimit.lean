/-
Ported from `Theorems/Thm_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Langlands.AnthropicFLT.P2M.Sol.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u₀ u v w w₁ w₂

theorem Algebra.exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R₀ : Type u₀) [CommRing R₀]
    (G : ι → Type v) [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FinitePresentation R₀ A]
    (B : Type w₂) [CommRing B] [Algebra R₀ B] [Algebra.FinitePresentation R₀ B]
    (e : R ⊗[R₀] A ≃ₐ[R] R ⊗[R₀] B) :
    ∃ (i : ι) (e₀ : G i ⊗[R₀] A ≃ₐ[G i] G i ⊗[R₀] B),
      ∀ x : G i ⊗[R₀] A,
        e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ A) x) =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (e₀ x) :=
  P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.solution R₀ G f R hR A B e
