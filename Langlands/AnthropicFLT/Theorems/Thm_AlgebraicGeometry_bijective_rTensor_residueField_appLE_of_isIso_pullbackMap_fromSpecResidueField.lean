/-
Ported from `Theorems/Thm_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

theorem AlgebraicGeometry.bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField
    {X Y Z : Scheme.{uz}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (W : Y.Opens) (hW : IsAffineOpen W) (hyW : y ∈ W)
    (U : X.Opens) (hU : IsAffineOpen U) (hUW : U ≤ q ⁻¹ᵁ W) (hhU : IsAffineOpen (h ⁻¹ᵁ U)) :
    letI : Algebra Γ(Y, W) Γ(X, U) := (q.appLE W U hUW).hom.toAlgebra
    letI : Algebra Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) := (q.appLE W U hUW ≫ h.appLE U (h ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    letI : Algebra Γ(Y, W) (Y.residueField y) := (Y.evaluation W y hyW).hom.toAlgebra
    Function.Bijective
      ((AlgHom.mk (h.appLE U (h ⁻¹ᵁ U) le_rfl).hom (fun _ => rfl) :
          Γ(X, U) →ₐ[Γ(Y, W)] Γ(Z, h ⁻¹ᵁ U)).toLinearMap.rTensor (Y.residueField y)) :=
  P2MW.S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField.solution p q h w y hy W hW hyW U hU hUW hhU
