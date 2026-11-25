/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf

/-!
# Multiplication by constants on `C(-, T)`

For a topological ring `T`, the multiplication by a constant `t : T` on the condensed abelian
group `T̲ = C(-, T)` (`Profinite.continuousMapRingObjMulLeft`) is the action of the constant
global section `t` of the condensed ring `T̲` on its regular module
(`Profinite.globalSmul_continuousMapConstRingHom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

/-- The action of a global section on the regular module is invariant under isomorphisms of
monoid objects. -/
lemma globalSmul_comp_hom_regular {C : Type*} [Category* C] [MonoidalCategory C] {A B : C}
    [MonObj A] [MonObj B] (e : A ≅ B) [IsMonHom e.hom] (σ : 𝟙_ C ⟶ A) :
    globalSmul (σ ≫ e.hom) (regular B) = e.inv ≫ globalSmul σ (regular A) ≫ e.hom := by
  change (λ_ B).inv ≫ (σ ≫ e.hom) ▷ B ≫ μ[B] = e.inv ≫ ((λ_ A).inv ≫ σ ▷ A ≫ μ[A]) ≫ e.hom
  rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def,
    Category.assoc, leftUnitor_inv_naturality_assoc, ← comp_whiskerRight_assoc,
    whisker_exchange_assoc, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The action of the image `ε ≫ F σ` of a global section on the regular module `F A` is the
image of the action of `σ` on the regular module `A`, for a lax monoidal functor `F`. -/
lemma globalSmul_regular_obj {C D : Type*} [Category* C] [MonoidalCategory C] [Category* D]
    [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] {A : C} [MonObj A] (σ : 𝟙_ C ⟶ A) :
    globalSmul (Functor.LaxMonoidal.ε F ≫ F.map σ) (regular (F.obj A)) =
      F.map (globalSmul σ (regular A)) := by
  rw [globalSmul, globalSmul, Functor.map_comp, Functor.map_comp,
    ← Functor.LaxMonoidal.left_unitality_inv, Category.assoc, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, comp_whiskerRight_assoc]
  rfl

end CategoryTheory.Mod

namespace Profinite

section MulLeft

variable (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- The multiplication by a constant `t : T` on the condensed abelian group `C(-, T)`. -/
noncomputable def continuousMapRingObjMulLeft (t : T) :
    continuousMapRingObj.{u} T ⟶ continuousMapRingObj T :=
  ⟨{ app _ := AddCommGrpCat.ofHom
        { toFun a := ULift.up (ContinuousMap.const _ t * a.down)
          map_zero' := congrArg ULift.up (mul_zero _)
          map_add' a b := congrArg ULift.up (mul_add _ a.down b.down) }
     naturality _ _ _ := rfl }⟩

lemma continuousMapRingObjMulLeft_app_apply (t : T) (S : Profinite.{u}ᵒᵖ)
    (a : ULift.{u + 1} C(S.unop, T)) :
    (continuousMapRingObjMulLeft T t).hom.app S a = ULift.up (ContinuousMap.const _ t * a.down) :=
  rfl

lemma continuousMapRingObjMulLeft_one :
    continuousMapRingObjMulLeft.{u} T 1 = 𝟙 _ := by
  ext S a
  exact congrArg ULift.up (one_mul _)

lemma nsmul_continuousMapRingObjMulLeft (n : ℕ) (t : T) :
    n • continuousMapRingObjMulLeft.{u} T t = continuousMapRingObjMulLeft T (n * t) := by
  ext S a
  refine congrArg ULift.up (ContinuousMap.ext fun s ↦ ?_)
  change n • (t * a.down s) = (n * t) * a.down s
  simp only [nsmul_eq_mul, _root_.mul_assoc]

end MulLeft

section GlobalSmul

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- On the presheaf `C(-, T)`, the constant global section `t` acts on the regular module by
multiplication by `t`. -/
lemma globalSmul_continuousMapConstSection_presheaf (t : T) :
    Mod.globalSmul ((continuousMapRingPresheaf.{u} T).ringHomΓCompForget₂
      (continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl) t).hom
      (Mod.regular (continuousMapRingPresheaf.{u} T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) =
    (continuousMapRingObjMulLeft.{u} T t).hom := by
  apply (cancel_epi (λ_ _).hom).1
  simp only [Mod.globalSmul, Iso.hom_inv_id_assoc]
  ext S : 2
  refine AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun n a ↦ ?_)
  change ((n.down : ULift.{u + 1} C(S.unop, T)) * ULift.up (ContinuousMap.const _ t)) *
      (show ULift.{u + 1} C(S.unop, T) from a) =
    ULift.up (ContinuousMap.const _ t * (n.down • (show ULift.{u + 1} C(S.unop, T) from a)).down)
  apply ULift.ext
  ext s
  change ((n.down : C(S.unop, T)) * ContinuousMap.const _ t *
    (show ULift.{u + 1} C(S.unop, T) from a).down : C(S.unop, T)) s =
      t * (n.down • (show ULift.{u + 1} C(S.unop, T) from a).down) s
  simp [zsmul_eq_mul]
  ring


/-- **The constant global section `t` of `T̲ = C(-, T)` acts on the regular module by
multiplication by `t`.** -/
lemma globalSmul_continuousMapConstRingHom (t : T) :
    Mod.globalSmul (continuousMapConstRingHom.{u} T t).hom
      (Mod.regular (continuousMapRingObj.{u} T)) = continuousMapRingObjMulLeft T t := by
  let J := coherentTopology Profinite.{u}
  let e := Sheaf.sheafifyRingPresheafIso.{u + 1, u, u + 1} J (continuousMapRingSheaf.{u} T)
  let sP := (continuousMapRingPresheaf.{u} T).ringHomΓCompForget₂
      (continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl) t
  have hσ : (continuousMapConstRingHom.{u} T t).hom =
      (Functor.LaxMonoidal.ε (presheafToSheaf J Ab.{u + 1}) ≫
        (presheafToSheaf J Ab.{u + 1}).map sP.hom) ≫ e.hom := rfl
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafifyRingPresheafIso_hom.{u + 1, u, u + 1} J _
  rw [hσ]
  erw [Mod.globalSmul_comp_hom_regular e]
  have h₁ : Mod.globalSmul (Functor.LaxMonoidal.ε (presheafToSheaf J Ab.{u + 1}) ≫
        (presheafToSheaf J Ab.{u + 1}).map sP.hom)
      (Mod.regular ((presheafToSheaf J Ab.{u + 1}).obj
        (continuousMapRingPresheaf.{u} T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}))) =
      (presheafToSheaf J Ab.{u + 1}).map (Mod.globalSmul sP.hom
        (Mod.regular (continuousMapRingPresheaf.{u} T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}))) := by
    rw [Mod.globalSmul, Mod.globalSmul, Functor.map_comp, Functor.map_comp,
      ← Functor.LaxMonoidal.left_unitality_inv, Category.assoc, Category.assoc,
      ← Functor.LaxMonoidal.μ_natural_left_assoc, comp_whiskerRight_assoc]
    rfl
  rw [globalSmul_continuousMapConstSection_presheaf] at h₁
  refine (congrArg (fun g ↦ e.inv ≫ g ≫ e.hom) h₁).trans ?_
  have h₂ := (sheafificationAdjunction J Ab.{u + 1}).counit.naturality
    (continuousMapRingObjMulLeft.{u} T t)
  exact (Iso.inv_comp_eq e).2 h₂


end GlobalSmul

end Profinite
