/-
Ported from `Theorems/Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H] :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens,
        Algebra K Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ f) W
    ∃ ε : ∀ (V : A.Opens) (_ : IsAffineOpen V),
        Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))),
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H,
      (∀ (V : A.Opens) (hV : IsAffineOpen V),
          IsAffineOpen ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
          ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
          ε V hV (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
              ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) = (1 : Γ(A, V)) ⊗ₜ[K] h) ∧
      (∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
          (s : Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))),
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
            ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map
              (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle)).op).hom s)) := by exact @_root_.P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen.solution K _ A f H _ _
