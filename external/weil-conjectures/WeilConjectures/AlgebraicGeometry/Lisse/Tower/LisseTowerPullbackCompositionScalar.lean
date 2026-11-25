/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerFixedPullbackScalar
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantCoherence
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerFixedPullbackScalar

/-! # Composition of ringed inverse images and restriction of coefficients

The composition comparison of module inverse images, conjugate to the restriction of
sections along the fibre-product pasting isomorphism, is compatible with the
restriction/pullback mates along the quotient coefficient maps.

## References

* Stacks Project, Modules on Sites, Tags 03D8 and 03DA
* Cohomology on Sites, Tag 0D6D
-/

public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

section Composition

variable {X Y W : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ X)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)

/-- The canonical adjunction for the identified-coefficient inverse image along `g`. -/
abbrev lisseTowerBaseAdjunction (g : Y ⟶ X) :
    proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op j)) (lisseTowerPulledRing d g j)
        (Iso.refl _) ⊣
      proEtaleRingModuleDirectImage g ((pbcAdicRings X d).obj (op j))
        (lisseTowerPulledRing d g j) (Iso.refl _) :=
  proEtaleRingModuleAdjunction g ((pbcAdicRings X d).obj (op j)) (lisseTowerPulledRing d g j)
    (Iso.refl _)

/-- The composite coefficient identification of the identity identifications. -/
theorem lisseTowerStep_coefficients :
    (Iso.refl (lisseTowerPulledRing d (f ≫ g) j)) =
      (proEtaleRingInverseImageComp f g).app ((pbcAdicRings X d).obj (op j)) ≪≫
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso (Iso.refl _) ≪≫
          (proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op j)) := by
  ext : 1
  simp

/-- The composite direct image is the direct image along the composite, by restriction
along the fibre-product pasting isomorphism. -/
def lisseTowerDirectImageComp :
    proEtaleRingModuleDirectImage (f ≫ g) ((pbcAdicRings X d).obj (op j))
        (lisseTowerPulledRing d (f ≫ g) j) (Iso.refl _) ≅
      lisseTowerStepDirectImage f g d j ⋙
        proEtaleRingModuleDirectImage g ((pbcAdicRings X d).obj (op j))
          (lisseTowerPulledRing d g j) (Iso.refl _) :=
  (proEtale_tensor_composition_unit f g ((pbcAdicRings X d).obj (op j))
    (lisseTowerPulledRing d g j) (lisseTowerPulledRing d (f ≫ g) j) (Iso.refl _)
    ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op j)))
    (Iso.refl _) (lisseTowerStep_coefficients f g d j)).choose

/-- The composition comparison of module inverse images. -/
def lisseTowerPullbackComp :
    proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op j)) (lisseTowerPulledRing d g j)
        (Iso.refl _) ⋙ lisseTowerStepPullback f g d j ≅
      proEtaleRingModulePullback (f ≫ g) ((pbcAdicRings X d).obj (op j))
        (lisseTowerPulledRing d (f ≫ g) j) (Iso.refl _) :=
  ((conjugateIsoEquiv ((lisseTowerBaseAdjunction d j g).comp (lisseTowerStepAdjunction f g d j))
    (lisseTowerBaseAdjunction d j (f ≫ g))).symm (lisseTowerDirectImageComp f g d j).symm).symm

/- Restriction of a section of a sheaf of modules along a morphism. -/
private def sheafMapElem {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} (M : SheafOfModules.{u + 1} R) {V V' : Cᵒᵖ} (h : V ⟶ V')
    (z : M.val.obj V) : M.val.obj V' :=
  M.val.map h z

private theorem sheafMapElem_naturality {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R} (ψ : M ⟶ N) {V V' : Cᵒᵖ}
    (h : V ⟶ V') (z : M.val.obj V) :
    ψ.val.app V' (sheafMapElem M h z) = sheafMapElem N h (ψ.val.app V z) :=
  PresheafOfModules.naturality_apply ψ.val h z

private theorem sheafMapElem_hom_inv {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} (N : SheafOfModules.{u + 1} R) {U T : C} (e : U ≅ T)
    (x : N.val.obj (op U)) : sheafMapElem N e.hom.op (sheafMapElem N e.inv.op x) = x := by
  unfold sheafMapElem
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, e.hom_inv_id, op_id,
    PresheafOfModules.map_id]
  rfl

private theorem sheafMapElem_inv_hom {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} (N : SheafOfModules.{u + 1} R) {U T : C} (e : U ≅ T)
    (x : N.val.obj (op T)) : sheafMapElem N e.inv.op (sheafMapElem N e.hom.op x) = x := by
  unfold sheafMapElem
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, e.inv_hom_id, op_id,
    PresheafOfModules.map_id]
  rfl

private theorem eq_sheafMapElem_inv {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} (N : SheafOfModules.{u + 1} R) {U T : C} (e : U ≅ T)
    {x : N.val.obj (op T)} {y : N.val.obj (op U)} (h : sheafMapElem N e.hom.op x = y) :
    x = sheafMapElem N e.inv.op y := by
  rw [← h, sheafMapElem_inv_hom]

private theorem sheafMapElem_restrictElem {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} S) {V V' : Cᵒᵖ} (h : V ⟶ V') (z : M.val.obj V) :
    sheafMapElem ((SheafOfModules.restrictScalars.{u + 1} φ).obj M) h (restrictElem φ M V z) =
      restrictElem φ M V' (sheafMapElem M h z) := rfl

private theorem directImageComp_hom_section
    (N : proEtaleRingModules W (lisseTowerPulledRing d (f ≫ g) j))
    (U : X.ProEt) (m : N.val.obj (op ((proEtaleBaseChange (f ≫ g)).obj U))) :
    ((lisseTowerDirectImageComp f g d j).hom.app N).val.app (op U) m =
      sheafMapElem N ((MorphismProperty.Over.pullbackComp f g).inv.app U).op m :=
  (proEtale_tensor_composition_unit f g ((pbcAdicRings X d).obj (op j))
    (lisseTowerPulledRing d g j) (lisseTowerPulledRing d (f ≫ g) j) (Iso.refl _)
    ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op j)))
    (Iso.refl _) (lisseTowerStep_coefficients f g d j)).choose_spec.choose_spec.1 N U m

private theorem directImageComp_inv_section
    (N : proEtaleRingModules W (lisseTowerPulledRing d (f ≫ g) j))
    (U : X.ProEt)
    (m : N.val.obj (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))) :
    ((lisseTowerDirectImageComp f g d j).inv.app N).val.app (op U) m =
      sheafMapElem N ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m := by
  have h := directImageComp_hom_section f g d j N U
    (((lisseTowerDirectImageComp f g d j).inv.app N).val.app (op U) m)
  have hi := congrArg (fun z ↦ z.val.app (op U) m)
    ((lisseTowerDirectImageComp f g d j).inv_hom_id_app N)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hi
  rw [hi] at h
  exact (sheafMapElem_hom_inv N ((MorphismProperty.Over.pullbackComp f g).app U) _).symm.trans
    (congrArg (sheafMapElem N ((MorphismProperty.Over.pullbackComp f g).hom.app U).op) h.symm)

private theorem pullbackComp_hom_section
    (N : proEtaleRingModules X ((pbcAdicRings X d).obj (op j)))
    (U : X.ProEt) (m : N.val.obj (op U)) :
    ((lisseTowerPullbackComp f g d j).hom.app N).val.app
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))
      (((lisseTowerStepAdjunction f g d j).unit.app
        ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op j))
          (lisseTowerPulledRing d g j) (Iso.refl _)).obj N)).val.app
        (op ((proEtaleBaseChange g).obj U))
        (((lisseTowerBaseAdjunction d j g).unit.app N).val.app (op U) m)) =
      sheafMapElem ((proEtaleRingModulePullback (f ≫ g) ((pbcAdicRings X d).obj (op j))
          (lisseTowerPulledRing d (f ≫ g) j) (Iso.refl _)).obj N)
        ((MorphismProperty.Over.pullbackComp f g).inv.app U).op
        (((lisseTowerBaseAdjunction d j (f ≫ g)).unit.app N).val.app (op U) m) := by
  have hc := congrArg (fun φ ↦ φ.val.app (op U) m) (unit_conjugateEquiv_symm
    ((lisseTowerBaseAdjunction d j g).comp (lisseTowerStepAdjunction f g d j))
    (lisseTowerBaseAdjunction d j (f ≫ g)) (lisseTowerDirectImageComp f g d j).inv N)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    Adjunction.comp_unit_app] at hc
  have h1 := (directImageComp_inv_section f g d j _ U _).symm.trans hc
  have h3 := sheafMapElem_naturality ((lisseTowerPullbackComp f g d j).hom.app N)
    ((MorphismProperty.Over.pullbackComp f g).hom.app U).op
    (((lisseTowerStepAdjunction f g d j).unit.app
        ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op j))
          (lisseTowerPulledRing d g j) (Iso.refl _)).obj N)).val.app
        (op ((proEtaleBaseChange g).obj U))
        (((lisseTowerBaseAdjunction d j g).unit.app N).val.app (op U) m))
  have h2 := congrArg (fun φ ↦ φ.val.app (op ((proEtaleBaseChange (f ≫ g)).obj U))
      (((lisseTowerBaseAdjunction d j (f ≫ g)).unit.app N).val.app (op U) m))
    ((lisseTowerPullbackComp f g d j).inv_hom_id_app N)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at h2
  exact eq_sheafMapElem_inv _ ((MorphismProperty.Over.pullbackComp f g).app U)
    (h3.symm.trans ((congrArg _ h1).trans h2))

/-- The restriction/pullback comparison for the identified-coefficient inverse image. -/
@[expose] def lisseTowerBaseRestriction (g : Y ⟶ X) (n : ℕ) :
    pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)) ⋙
        proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op (n + 1)))
          (lisseTowerPulledRing d g (n + 1)) (Iso.refl _) ⟶
      proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
          (lisseTowerPulledRing d g n) (Iso.refl _) ⋙
        pbcRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) :=
  proEtaleRingRestrictionPullbackInv g ((pbcAdicRings X d).obj (op (n + 1)))
    ((pbcAdicRings X d).obj (op n)) (lisseTowerPulledRing d g (n + 1))
    (lisseTowerPulledRing d g n) (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
    ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- The base restriction/pullback comparison, unfolded. -/
theorem lisseTowerBaseRestriction_eq (g : Y ⟶ X) (n : ℕ) :
    lisseTowerBaseRestriction d g n =
      proEtaleRingRestrictionPullbackInv g ((pbcAdicRings X d).obj (op (n + 1)))
        ((pbcAdicRings X d).obj (op n)) (lisseTowerPulledRing d g (n + 1))
        (lisseTowerPulledRing d g n) (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
        ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
        (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm) :=
  rfl

/-- The base restriction/pullback comparison is invertible. -/
instance lisseTowerBaseRestriction_isIso (g : Y ⟶ X) (n : ℕ) :
    IsIso (lisseTowerBaseRestriction d g n) :=
  proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _

private theorem compExt (K : proEtaleRingModules X ((pbcAdicRings X d).obj (op j)))
    {M : proEtaleRingModules W (lisseTowerPulledRing d (f ≫ g) j)}
    (x y : (lisseTowerStepPullback f g d j).obj
      ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op j))
          (lisseTowerPulledRing d g j) (Iso.refl _)).obj K) ⟶ M)
    (h : ∀ (U : X.ProEt) (m : K.val.obj (op U)),
      x.val.app (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))
        (((lisseTowerStepAdjunction f g d j).unit.app
          ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op j))
            (lisseTowerPulledRing d g j) (Iso.refl _)).obj K)).val.app
          (op ((proEtaleBaseChange g).obj U))
          (((lisseTowerBaseAdjunction d j g).unit.app K).val.app (op U) m)) =
      y.val.app (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))
        (((lisseTowerStepAdjunction f g d j).unit.app
          ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op j))
            (lisseTowerPulledRing d g j) (Iso.refl _)).obj K)).val.app
          (op ((proEtaleBaseChange g).obj U))
          (((lisseTowerBaseAdjunction d j g).unit.app K).val.app (op U) m))) : x = y := by
  refine adj_ext ((lisseTowerBaseAdjunction d j g).comp (lisseTowerStepAdjunction f g d j))
    _ _ ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun U ↦ ?_))
  ext m
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    Adjunction.comp_unit_app]
  exact h U.unop m

private theorem comp_lhs_unit (n : ℕ) (N : proEtaleRingModules X ((pbcAdicRings X d).obj (op n)))
    (U : X.ProEt) (m : N.val.obj (op U)) :
    ((lisseTowerStepPullback f g d (n + 1)).map ((lisseTowerBaseRestriction d g n).app N)).val.app
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))
      (((lisseTowerStepAdjunction f g d (n + 1)).unit.app
        ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op (n + 1)))
          (lisseTowerPulledRing d g (n + 1)) (Iso.refl _)).obj
            ((pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N))).val.app
        (op ((proEtaleBaseChange g).obj U))
        (((lisseTowerBaseAdjunction d (n + 1) g).unit.app
          ((pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N)).val.app (op U)
          (restrictElem ((adicLisseForget X).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
            N (op U) m))) =
      ((lisseTowerStepAdjunction f g d (n + 1)).unit.app
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).obj
          ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
            (lisseTowerPulledRing d g n) (Iso.refl _)).obj N))).val.app
        (op ((proEtaleBaseChange g).obj U))
        (restrictElem ((adicLisseForget Y).map ((adicTowerInverseImage g).map
            (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
          ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
            (lisseTowerPulledRing d g n) (Iso.refl _)).obj N) (op ((proEtaleBaseChange g).obj U))
          (((lisseTowerBaseAdjunction d n g).unit.app N).val.app (op U) m)) := by
  have hn := congrArg (fun φ ↦ φ.val.app (op ((proEtaleBaseChange g).obj U))
      (((lisseTowerBaseAdjunction d (n + 1) g).unit.app
          ((pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N)).val.app (op U)
          (restrictElem ((adicLisseForget X).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
            N (op U) m)))
    ((lisseTowerStepAdjunction f g d (n + 1)).unit_naturality
      ((lisseTowerBaseRestriction d g n).app N))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hn
  exact hn.trans (congrArg _ (pullbackInv_unit g ((pbcAdicRings X d).obj (op (n + 1)))
    ((pbcAdicRings X d).obj (op n)) (lisseTowerPulledRing d g (n + 1))
    (lisseTowerPulledRing d g n) (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
    ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm) N (op U) m))

private theorem comp_lhs_section (n : ℕ) (N : proEtaleRingModules X ((pbcAdicRings X d).obj (op n)))
    (U : X.ProEt) (m : N.val.obj (op U)) :
    ((pbcRestrict ((adicTowerInverseImage (f ≫ g)).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
      ((lisseTowerPullbackComp f g d n).hom.app N)).val.app
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))
    (((lisseTowerStepRestriction f g d n).app
      ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
            (lisseTowerPulledRing d g n) (Iso.refl _)).obj N)).val.app
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))
    (((lisseTowerStepPullback f g d (n + 1)).map ((lisseTowerBaseRestriction d g n).app N)).val.app
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))
      (((lisseTowerStepAdjunction f g d (n + 1)).unit.app
        ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op (n + 1)))
          (lisseTowerPulledRing d g (n + 1)) (Iso.refl _)).obj
            ((pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N))).val.app
        (op ((proEtaleBaseChange g).obj U))
        (((lisseTowerBaseAdjunction d (n + 1) g).unit.app
          ((pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N)).val.app (op U)
          (restrictElem ((adicLisseForget X).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
            N (op U) m))))) =
      restrictElem ((adicLisseForget W).map ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
        ((proEtaleRingModulePullback (f ≫ g) ((pbcAdicRings X d).obj (op n))
          (lisseTowerPulledRing d (f ≫ g) n) (Iso.refl _)).obj N)
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))
        (sheafMapElem ((proEtaleRingModulePullback (f ≫ g) ((pbcAdicRings X d).obj (op n))
          (lisseTowerPulledRing d (f ≫ g) n) (Iso.refl _)).obj N)
          ((MorphismProperty.Over.pullbackComp f g).inv.app U).op
          (((lisseTowerBaseAdjunction d n (f ≫ g)).unit.app N).val.app (op U) m)) :=
  chain3_eq (comp_lhs_unit f g d n N U m)
    (chain2_eq (pullbackInv_unit f (lisseTowerPulledRing d g (n + 1))
      (lisseTowerPulledRing d g n) (lisseTowerPulledRing d (f ≫ g) (n + 1))
      (lisseTowerPulledRing d (f ≫ g) n)
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      ((adicTowerInverseImage (f ≫ g)).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op (n + 1))))
      ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op n)))
      (lisseTowerStep_comm f g d n)
      ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
            (lisseTowerPulledRing d g n) (Iso.refl _)).obj N) (op ((proEtaleBaseChange g).obj U))
      (((lisseTowerBaseAdjunction d n g).unit.app N).val.app (op U) m))
      ((restrictScalars_map_restrictElem _ _ _ _).trans
        (congrArg (restrictElem ((adicLisseForget W).map ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
        ((proEtaleRingModulePullback (f ≫ g) ((pbcAdicRings X d).obj (op n))
          (lisseTowerPulledRing d (f ≫ g) n) (Iso.refl _)).obj N)
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U))))
        (pullbackComp_hom_section f g d n N U m))))
private theorem baseRestriction_unit (g : Y ⟶ X) (n : ℕ)
    (N : proEtaleRingModules X ((pbcAdicRings X d).obj (op n)))
    (U : X.ProEt) (m : N.val.obj (op U)) :
    ((lisseTowerBaseRestriction d g n).app N).val.app (op ((proEtaleBaseChange g).obj U))
      (((lisseTowerBaseAdjunction d (n + 1) g).unit.app
          ((pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N)).val.app (op U)
          (restrictElem ((adicLisseForget X).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
            N (op U) m)) =
      restrictElem ((adicLisseForget Y).map ((adicTowerInverseImage g).map
            (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
          ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
            (lisseTowerPulledRing d g n) (Iso.refl _)).obj N) (op ((proEtaleBaseChange g).obj U))
          (((lisseTowerBaseAdjunction d n g).unit.app N).val.app (op U) m) :=
  pullbackInv_unit g ((pbcAdicRings X d).obj (op (n + 1)))
    ((pbcAdicRings X d).obj (op n)) (lisseTowerPulledRing d g (n + 1))
    (lisseTowerPulledRing d g n) (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
    ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm) N (op U) m



private theorem comp_rhs_restrict (n : ℕ)
    (N : proEtaleRingModules X ((pbcAdicRings X d).obj (op n)))
    (U : X.ProEt) (m : N.val.obj (op U)) :
    ((lisseTowerBaseRestriction d (f ≫ g) n).app N).val.app
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))
      (sheafMapElem ((proEtaleRingModulePullback (f ≫ g) ((pbcAdicRings X d).obj (op (n + 1)))
          (lisseTowerPulledRing d (f ≫ g) (n + 1)) (Iso.refl _)).obj
            ((pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N))
          ((MorphismProperty.Over.pullbackComp f g).inv.app U).op
        (((lisseTowerBaseAdjunction d (n + 1) (f ≫ g)).unit.app
          ((pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N)).val.app (op U)
          (restrictElem ((adicLisseForget X).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
            N (op U) m))) =
      restrictElem ((adicLisseForget W).map ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
        ((proEtaleRingModulePullback (f ≫ g) ((pbcAdicRings X d).obj (op n))
          (lisseTowerPulledRing d (f ≫ g) n) (Iso.refl _)).obj N)
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))
        (sheafMapElem ((proEtaleRingModulePullback (f ≫ g) ((pbcAdicRings X d).obj (op n))
          (lisseTowerPulledRing d (f ≫ g) n) (Iso.refl _)).obj N)
          ((MorphismProperty.Over.pullbackComp f g).inv.app U).op
          (((lisseTowerBaseAdjunction d n (f ≫ g)).unit.app N).val.app (op U) m)) :=
  (sheafMapElem_naturality ((lisseTowerBaseRestriction d (f ≫ g) n).app N)
    ((MorphismProperty.Over.pullbackComp f g).inv.app U).op _).trans
    ((congrArg (sheafMapElem _ ((MorphismProperty.Over.pullbackComp f g).inv.app U).op)
      (baseRestriction_unit d (f ≫ g) n N U m)).trans (sheafMapElem_restrictElem _ _ _ _))

/-- The composition comparison of module inverse images is compatible with the
restriction/pullback comparisons along the consecutive quotient of coefficients. -/
theorem lisseTowerPullbackComp_restriction (n : ℕ)
    (N : proEtaleRingModules X ((pbcAdicRings X d).obj (op n))) :
    (lisseTowerStepPullback f g d (n + 1)).map ((lisseTowerBaseRestriction d g n).app N) ≫
        (lisseTowerStepRestriction f g d n).app
          ((proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
            (lisseTowerPulledRing d g n) (Iso.refl _)).obj N) ≫
        (pbcRestrict ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
          ((lisseTowerPullbackComp f g d n).hom.app N) =
      (lisseTowerPullbackComp f g d (n + 1)).hom.app
          ((pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N) ≫
        (lisseTowerBaseRestriction d (f ≫ g) n).app N := by
  refine compExt f g d (n + 1) _ _ _ (fun U m ↦ ?_)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact (comp_lhs_section f g d n N U m).trans
    ((chain2_eq (pullbackComp_hom_section f g d (n + 1) _ U _)
      (comp_rhs_restrict f g d n N U m)).symm)

end Composition

end AlgebraicGeometry.Scheme
