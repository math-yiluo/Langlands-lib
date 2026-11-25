/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor

/-!
# Image of stalk tensor multiplication

Source: Stacks Project, Modules, Tags 01AG and 01CB.
(blueprint: lem-weil-pbc-ideal-multiplication-stalk-range-tensor).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open AlgebraicGeometry
noncomputable section

namespace AlgebraicGeometry.Scheme

/-- The module stalk map sends a section germ to the germ of its sectionwise image. -/
private theorem stalk_map_germ {X : Scheme.{u}} (x : X) {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) (hx : x ∈ U) (m : M.val.obj (Opposite.op U)) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map f
      (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
    TopCat.Presheaf.germ N.val.presheaf U x hx ((f.val.app (Opposite.op U)) m) := by
  change RingedSpace.stalkAddMap X.toRingedSpace x f _ = _
  dsimp only [RingedSpace.stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of sheaf tensor multiplication has image equal to the ideal generated
by the stalk image of the ideal map. This is the pure-tensor calculation in the
proof of `ideal_multiplication_stalk_range`; it follows from the stalk tensor
comparison and the germ formula for `e`.
Source: Stacks Project, Modules, Lemmas 01AG and 01CB.
(blueprint: lem-weil-pbc-ideal-multiplication-stalk-range-tensor).
-/
theorem stalk_tensor_multiplication_range {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) (x : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    LinearMap.range (S.map (ι ▷ F ≫ (λ_ F).hom)).hom =
      (LinearMap.range (S.map ι ≫ e.hom).hom : Ideal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let : MonoidalCategory (SheafOfModules X.ringCatSheaf) :=
    SheafOfModules.monoidalCategory X.sheaf
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let O := SheafOfModules.unit X.ringCatSheaf
  obtain ⟨Φ, hΦ, hn⟩ := SheafOfModules.stalkTensorIso X.toRingedSpace x
  have hunit (a : S.obj O) (b : S.obj F) :
      S.map (λ_ F).hom ((Φ O F).inv (a ⊗ₜ[X.presheaf.stalk x] b)) = e.hom a • b := by
    obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq O.val.presheaf a
    obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf b
    have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← TopCat.Presheaf.germ_res_apply O.val.presheaf
      (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
      ← TopCat.Presheaf.germ_res_apply F.val.presheaf
      (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx t]
    let r' : Γ(X, U ⊓ V) := O.val.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r
    let t' : Γ(F, U ⊓ V) := F.val.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op t
    let P := O.val ⊗ F.val
    let θ := (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
        (SheafOfModules.forget X.ringCatSheaf).map
          (SheafOfModules.tensorObjIsoSheafification O F).inv
    have hg := hΦ O F (U ⊓ V) hx r' t'
    have hi : (Φ O F).inv
        ((TopCat.Presheaf.germ O.val.presheaf (U ⊓ V) x hx r') ⊗ₜ[X.presheaf.stalk x]
          TopCat.Presheaf.germ F.val.presheaf (U ⊓ V) x hx t') =
        TopCat.Presheaf.germ (O ⊗ F).val.presheaf (U ⊓ V) x hx
          ((θ.app (Opposite.op (U ⊓ V))) (r' ⊗ₜ[Γ(X, U ⊓ V)] t')) := by
      rw [← hg]
      exact ConcreteCategory.congr_hom (Φ O F).hom_inv_id _
    erw [hi, stalk_map_germ]
    change TopCat.Presheaf.germ F.val.presheaf (U ⊓ V) x hx
      ((λ_ F).hom.app (U ⊓ V) (Modules.tmulSection r' t')) = _
    have hu := Modules.leftUnitor_hom_app_tmulSection (M := F) r' t'
    change (λ_ F).hom.app (U ⊓ V) (Modules.tmulSection r' t') = r' • t' at hu
    rw [hu]
    rw [he, PresheafOfModules.germ_smul (R := X.presheaf) F.val]
    rfl
  have hmul (a : S.obj J) (b : S.obj F) :
      S.map (ι ▷ F ≫ (λ_ F).hom)
        ((Φ J F).inv (a ⊗ₜ[X.presheaf.stalk x] b)) =
      (S.map ι ≫ e.hom) a • b := by
    have hnat := hn J F O F ι (𝟙 F)
    rw [tensorHom_id, S.map_id, tensorHom_id] at hnat
    have hh := ConcreteCategory.congr_hom hnat
      ((Φ J F).inv (a ⊗ₜ[X.presheaf.stalk x] b))
    simp only [ModuleCat.comp_apply] at hh
    have hc : (Φ O F).hom (S.map (ι ▷ F)
        ((Φ J F).inv (a ⊗ₜ[X.presheaf.stalk x] b))) =
        S.map ι a ⊗ₜ[X.presheaf.stalk x] b := by
      have hiJF : (Φ J F).hom ((Φ J F).inv
          (a ⊗ₜ[X.presheaf.stalk x] b)) = a ⊗ₜ[X.presheaf.stalk x] b :=
        ConcreteCategory.congr_hom (Φ J F).inv_hom_id _
      rw [hiJF, ModuleCat.MonoidalCategory.whiskerRight_apply] at hh
      exact hh
    have hc' := congrArg (fun z ↦ (Φ O F).inv z) hc
    simp only [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply] at hc'
    rw [S.map_comp]
    change S.map (λ_ F).hom (S.map (ι ▷ F)
      ((Φ J F).inv (a ⊗ₜ[X.presheaf.stalk x] b))) = _
    rw [hc', hunit]
    rfl
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have hz : (Φ J F).inv ((Φ J F).hom z) = z :=
      ConcreteCategory.congr_hom (Φ J F).hom_inv_id z
    rw [← hz]
    generalize (Φ J F).hom z = q
    induction q using TensorProduct.inductionOn with
    | tmul a b =>
      rw [hmul]
      exact Submodule.smul_mem_smul ⟨a, rfl⟩ (Submodule.mem_top : b ∈ ⊤)
    | add q q' hq hq' =>
      simpa only [map_add] using Submodule.add_mem _ hq hq'
  · apply Submodule.smul_le.mpr
    rintro r ⟨a, rfl⟩ b _
    exact ⟨(Φ J F).inv (a ⊗ₜ[X.presheaf.stalk x] b), hmul a b⟩

end AlgebraicGeometry.Scheme
end
