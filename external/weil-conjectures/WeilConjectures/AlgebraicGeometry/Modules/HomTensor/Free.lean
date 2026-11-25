/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Presheaf

/-!
# The morphism Hom(M, R) ⊗ N ⟶ Hom(M, N) of sheaves of modules for a free M

If a sheaf of modules `M` is free of finite rank on an object `U`, then
`Hom(M, R) ⊗ N ⟶ Hom(M, N)` is bijective on sections over every object over `U`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] {R : Sheaf J CommRingCat.{u}}

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

variable {U : C} in
/-- If `M` is free of finite rank on `U`, then `Hom(M, R) ⊗ N ⟶ Hom(M, N)` is bijective on
sections over every `V ⟶ U`. -/
lemma dualTensorHom_app_bijective_of_iso_free [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] (M N : SheafOfModules.{u} 𝓡)
    {I : Type u} [Finite I] (e : free I ≅ M.over U) {V : C} (g : V ⟶ U) :
    Function.Bijective ((PresheafOfModules.dualTensorHom M.val N.val).app (op V)) := by
  classical
  let := Fintype.ofFinite I
  let S (j : I) : (unit 𝓡).over U ⟶ M.over U := Sigma.ι (fun _ ↦ unit _) j ≫ e.hom
  let Cc (j : I) : M.over U ⟶ (unit 𝓡).over U :=
    e.inv ≫ Sigma.desc (fun k ↦ if k = j then 𝟙 (unit _) else 0)
  have hsc (i j : I) : S j ≫ Cc i = if j = i then 𝟙 _ else 0 := by
    simp only [S, Cc, Category.assoc, Iso.hom_inv_id_assoc, Sigma.ι_comp_desc]
    rfl
  have hsum : ∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (unit _) else 0) ≫
      Sigma.ι (fun _ : I ↦ unit ((𝓡).over U)) i = 𝟙 (free I) := by
    refine Sigma.hom_ext _ _ fun k ↦ ?_
    rw [Preadditive.comp_sum, Finset.sum_eq_single k (fun b _ hb ↦ by simp [Ne.symm hb])
      (by simp)]
    simp only [Sigma.ι_comp_desc_assoc]
    exact (Category.comp_id _).symm
  have htot : ∑ i, Cc i ≫ S i = 𝟙 _ := by
    calc ∑ i, Cc i ≫ S i = e.inv ≫ (∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (unit _) else 0) ≫
          Sigma.ι (fun _ : I ↦ unit ((𝓡).over U)) i) ≫ e.hom := by
          simp only [Cc, S, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
          rfl
      _ = 𝟙 _ := by rw [hsum, Category.id_comp, Iso.inv_hom_id]
  refine PresheafOfModules.dualTensorHom_app_bijective_of_hom (P := N.val) (U := U)
    (fun j ↦ toRestrictOverHom (S j)) (fun j ↦ toRestrictOverHom (Cc j)) (fun i j ↦ ?_) ?_ g
  · refine (congrArg toRestrictOverHom (hsc i j)).trans ?_
    split_ifs
    · exact toRestrictOverHom_id _
    · exact toRestrictOverHom_zero _ _
  · exact (toRestrictOverHom_sum Finset.univ (fun i ↦ Cc i ≫ S i)).symm.trans
      ((congrArg toRestrictOverHom htot).trans (toRestrictOverHom_id M))

end SheafOfModules
