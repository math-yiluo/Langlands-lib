/-
Ported from `Theorems/Thm_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the FLT commands `p2m_export`, `p2m_open` and `p2m_reactivate` are replaced by `export`, `open` and `open scoped`; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TensorProduct
open _root_.AlgebraicGeometry hiding exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen

universe u

theorem AlgebraicGeometry.exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H]
    {B : Scheme.{u}} (fB : B ⟶ Spec (CommRingCat.of H)) (π : B ⟶ A)
    (hB : IsPullback π fB f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKB : ∀ W : B.Opens, Algebra K Γ(B, W) := fun W => Scheme.TwoAffineOpenCover.algebraOfHom (π ≫ f) W
    ∃ ε : ∀ (V : A.Opens) (_ : IsAffineOpen V), Γ(B, π ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H,
      (∀ (V : A.Opens) (hV : IsAffineOpen V), IsAffineOpen (π ⁻¹ᵁ V)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)), ε V hV ((π.app V).hom a) = a ⊗ₜ[K] (1 : H)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
          ε V hV ((fB.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) =
            (1 : Γ(A, V)) ⊗ₜ[K] h) ∧
      (∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V) (s : Γ(B, π ⁻¹ᵁ V)),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
            ε V' hV' ((B.presheaf.map (homOfLE (π.preimage_mono hle)).op).hom s)) :=
  P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.solution K f H fB π hB
