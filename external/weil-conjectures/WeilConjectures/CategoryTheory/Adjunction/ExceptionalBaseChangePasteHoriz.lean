/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ExceptionalTensorMap

/-!
# Horizontal pasting of exceptional base changes (light imports)

`CategoryTheory.Adjunction.exceptionalBaseChange_eq_mateEquiv_inv_app` identifies the exceptional
base change `CategoryTheory.Adjunction.exceptionalBaseChange` of an invertible base change `bc`
with the component of the mate of `inv bc`, and
`CategoryTheory.Adjunction.exceptionalBaseChange_paste_horiz'` is the horizontal pasting law of
exceptional base changes. The latter is a copy of
`CategoryTheory.Adjunction.exceptionalBaseChange_paste_horiz`
(`WeilConjectures.SmoothPurity.UpperShriekBaseChangePasting`), placed here so that it can be used
with finite étale coefficients without the condensed import closure of that file.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

section Mate

variable {𝒳 𝒴 𝒳' 𝒴' : Type*} [Category* 𝒳] [Category* 𝒴] [Category* 𝒳'] [Category* 𝒴']
  {L : 𝒳 ⥤ 𝒴} {R : 𝒴 ⥤ 𝒳} {L' : 𝒳' ⥤ 𝒴'} {R' : 𝒴' ⥤ 𝒳'} {v : 𝒴 ⥤ 𝒴'} {u : 𝒳 ⥤ 𝒳'}
  (a : L ⊣ R) (a' : L' ⊣ R') (bc : L ⋙ v ⟶ u ⋙ L') [IsIso bc]

/-- The exceptional base change is the component of the mate of the inverse of the base
change. -/
lemma exceptionalBaseChange_eq_mateEquiv_inv_app (N : 𝒴) :
    exceptionalBaseChange a a' bc N = (mateEquiv a a' (inv bc)).app N := by
  rw [exceptionalBaseChange, Adjunction.homEquiv_unit]
  simp [mateEquiv_apply, NatIso.isIso_inv_app]

end Mate

section Paste

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]
  {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {L : C₃ ⥤ D₃} {R : D₃ ⥤ C₃}
  {u₁ : C₂ ⥤ C₁} {u₂ : C₃ ⥤ C₂} {u : C₃ ⥤ C₁} {v₁ : D₂ ⥤ D₁} {v₂ : D₃ ⥤ D₂} {v : D₃ ⥤ D₁}

/-- **Horizontal pasting of exceptional base changes** (copy of
`CategoryTheory.Adjunction.exceptionalBaseChange_paste_horiz`): let `bc₂ : L ⋙ v₂ ⟶ u₂ ⋙ L₂` and
`bc₁ : L₂ ⋙ v₁ ⟶ u₁ ⋙ L₁` be invertible base changes for adjunctions `L ⊣ R`, `L₂ ⊣ R₂` and
`L₁ ⊣ R₁`, and let `bc : L ⋙ v ⟶ u ⋙ L₁` be their pasting through `u ≅ u₂ ⋙ u₁` and
`v ≅ v₂ ⋙ v₁`. Then the exceptional base change of `bc` is `u₁` of that of `bc₂` followed by that
of `bc₁`, through the same isomorphisms. -/
lemma exceptionalBaseChange_paste_horiz' (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (eu : u ≅ u₂ ⋙ u₁) (ev : v ≅ v₂ ⋙ v₁) (bc₁ : L₂ ⋙ v₁ ⟶ u₁ ⋙ L₁) [IsIso bc₁]
    (bc₂ : L ⋙ v₂ ⟶ u₂ ⋙ L₂) [IsIso bc₂] (bc : L ⋙ v ⟶ u ⋙ L₁) [IsIso bc]
    (h : ∀ K, bc.app K = ev.hom.app (L.obj K) ≫ v₁.map (bc₂.app K) ≫ bc₁.app (u₂.obj K) ≫
      L₁.map (eu.inv.app K)) (N : D₃) :
    exceptionalBaseChange a a₁ bc N =
      eu.hom.app (R.obj N) ≫ u₁.map (exceptionalBaseChange a a₂ bc₂ N) ≫
        exceptionalBaseChange a₂ a₁ bc₁ (v₂.obj N) ≫ R₁.map (ev.inv.app N) := by
  apply (a₁.homEquiv _ _).symm.injective
  have h₂ : L₂.map (exceptionalBaseChange a a₂ bc₂ N) ≫ a₂.counit.app (v₂.obj N) =
      inv (bc₂.app (R.obj N)) ≫ v₂.map (a.counit.app N) :=
    (a₂.homEquiv _ _).symm_apply_apply _
  have hinv (K : C₃) : inv (bc.app K) = L₁.map (eu.hom.app K) ≫ inv (bc₁.app (u₂.obj K)) ≫
      v₁.map (inv (bc₂.app K)) ≫ ev.inv.app (L.obj K) := by
    rw [IsIso.inv_eq_of_hom_inv_id]
    rw [h]
    simp [← Functor.map_comp_assoc]
  have h₀ : (a₁.homEquiv _ _).symm (exceptionalBaseChange a a₁ bc N) =
      inv (bc.app (R.obj N)) ≫ v.map (a.counit.app N) :=
    (a₁.homEquiv _ _).symm_apply_apply _
  have h₁ : (a₁.homEquiv _ _).symm (exceptionalBaseChange a₂ a₁ bc₁ (v₂.obj N)) =
      inv (bc₁.app (R₂.obj (v₂.obj N))) ≫ v₁.map (a₂.counit.app (v₂.obj N)) :=
    (a₁.homEquiv _ _).symm_apply_apply _
  have n₁ := (inv bc₁).naturality (exceptionalBaseChange a a₂ bc₂ N)
  have n₂ := ev.inv.naturality (a.counit.app N)
  simp only [Functor.comp_map, NatIso.isIso_inv_app, Functor.comp_obj, Functor.id_obj] at n₁ n₂
  rw [h₀, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, h₁, hinv]
  simp only [Category.assoc]
  congr 1
  rw [reassoc_of% n₁, ← Functor.map_comp_assoc, h₂]
  simp [n₂]

end Paste

end CategoryTheory.Adjunction
