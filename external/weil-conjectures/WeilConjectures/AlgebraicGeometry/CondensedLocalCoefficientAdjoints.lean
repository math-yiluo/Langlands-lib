/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all WeilConjectures.AlgebraicGeometry.SplitCoefficientDerivedFaithful

/-!
# Canonical local scalar adjoints at every finite coefficient stage

Source: archived ModuleObject/Colimit/TwoColimit.lean, (Obj) overlap descent paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonObj MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
private lemma mono_pulled_coefficient_unit
    (T X Y : Scheme.{u}) (f : X ⟶ T) (g : Y ⟶ X)
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))) :
    Mono ((Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).unit.app P) := by
  let H := upperStarFromPoint T
  let K := upperStar Ab.{u + 1} f
  let J := upperStar Ab.{u + 1} g
  let r := J.map (K.map (H.map (Profinite.condensedProjection ℓ E)))
  have hlin := CategoryTheory.mapLinear J _ _
    (CategoryTheory.mapLinear K _ _
      (CategoryTheory.mapLinear H _ _ (Profinite.condensedProjection_linear ℓ E)))
  have hret : J.map (K.map (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ≫ r = 𝟙 _ := by
    change J.map (K.map (H.map _)) ≫ J.map (K.map (H.map _)) = 𝟙 _
    rw [← J.map_comp, ← K.map_comp, ← H.map_comp,
      Profinite.condensedProjection_retract, H.map_id, K.map_id, J.map_id]
  have hs := unit_retract _ _ _ r hlin hret
  have hsP : (Mod.extendRestrictAdjunction (J.map (K.map
      (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).unit.app P ≫
        (retractNat _ _ _ r hlin).app P = 𝟙 P := congr_app hs P
  exact ⟨fun a b h ↦ by
    have h' := congrArg (· ≫ (retractNat _ _ _ r hlin).app P) h
    simp only [Category.assoc] at h'
    change a ≫ ((Mod.extendRestrictAdjunction (J.map (K.map
        (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).unit.app P ≫
        (retractNat _ _ _ r hlin).app P) =
      b ≫ ((Mod.extendRestrictAdjunction (J.map (K.map
        (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).unit.app P ≫
        (retractNat _ _ _ r hlin).app P) at h'
    rw [hsP] at h'
    change a ≫ 𝟙 P = b ≫ 𝟙 P at h'
    exact (Category.comp_id a).symm.trans (h'.trans (Category.comp_id b))⟩

set_option backward.isDefEq.respectTransparency false

section ScalarUnits
open MonoidalCategory
variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  {R S A : C} [MonObj R] [MonObj S] [MonObj A]
  [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ A) [IsMonHom ψ]

omit [IsCommMonObj S] in
/-- The scalar-extension adjunction has the explicit extension unit. -/
lemma scalar_unit (P : Mod C R) :
    (Mod.extendRestrictAdjunction φ).unit.app P = Mod.extendUnit φ P := by
  change Mod.extendUnit φ P ≫ (Mod.comap φ).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma scalar_comp_unit (P : Mod C R) :
    (Mod.extendUnit φ P).hom ≫
      (Mod.extendUnit ψ ((Mod.extendScalars φ).obj P)).hom ≫
        (((Mod.extendScalarsComp φ ψ).inv.app P).hom) =
      (Mod.extendUnit (φ ≫ ψ) P).hom := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Mod.extendRestrictAdjunction (φ ≫ ψ))
    (((Mod.extendRestrictAdjunction φ).comp (Mod.extendRestrictAdjunction ψ)).ofNatIsoRight
      (Mod.comapComp φ ψ).symm) P
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    CategoryTheory.Functor.whiskerLeft_app,
    Adjunction.comp_unit_app, scalar_unit] at h
  have h' := congrArg (fun k ↦ k.hom) h
  change (Mod.extendUnit (φ ≫ ψ) P).hom ≫
      ((Mod.extendScalarsComp φ ψ).hom.app P).hom =
    ((Mod.extendUnit φ P).hom ≫
      (Mod.extendUnit ψ ((Mod.extendScalars φ).obj P)).hom) ≫ 𝟙 _ at h'
  rw [Category.comp_id] at h'
  rw [← Category.assoc]
  apply Eq.trans (congrArg (· ≫ ((Mod.extendScalarsComp φ ψ).inv.app P).hom) h'.symm)
  have hi := congrArg (fun k ↦ k.hom) ((Mod.extendScalarsComp φ ψ).hom_inv_id_app P)
  change ((Mod.extendScalarsComp φ ψ).hom.app P).hom ≫
      ((Mod.extendScalarsComp φ ψ).inv.app P).hom = 𝟙 _ at hi
  rw [Category.assoc, hi]
  exact Category.comp_id _

omit [IsCommMonObj S] in
private lemma scalar_eq_unit {χ : R ⟶ A} [IsMonHom χ] (h : φ ≫ ψ = χ)
    (P : Mod C R) :
    (Mod.extendUnit (φ ≫ ψ) P).hom ≫
      (((Mod.extendScalarsIsoOfEq h).hom.app P).hom) = (Mod.extendUnit χ P).hom := by
  have h' := Adjunction.unit_leftAdjointUniq_hom_app
    (Mod.extendRestrictAdjunction (φ ≫ ψ))
    ((Mod.extendRestrictAdjunction χ).ofNatIsoRight (Mod.comapCongr h).symm) P
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    CategoryTheory.Functor.whiskerLeft_app,
    scalar_unit] at h'
  have hh := congrArg (fun k ↦ k.hom) h'
  change (Mod.extendUnit (φ ≫ ψ) P).hom ≫
      ((Mod.extendScalarsIsoOfEq h).hom.app P).hom =
    (Mod.extendUnit χ P).hom ≫ 𝟙 _ at hh
  simpa only [Category.comp_id] using hh

omit [IsCommMonObj S] in
/-- The mixed-scalar comparison takes the first extension unit to the composite unit. -/
lemma mixedScalarMap_unit {χ : R ⟶ A} [IsMonHom χ]
    (h : φ ≫ ψ = χ) (P : Mod C R) :
    (Mod.extendUnit φ P).hom ≫
      (Mod.mixedScalarMap φ χ (𝟙 S) ψ ψ h (by simp) P).hom =
        (Mod.extendUnit χ P).hom := by
  dsimp only [Mod.mixedScalarMap, Mod.Hom.mk']
  exact Mod.extendUnitHom_extendHom φ _

private lemma tensorAdjoint_unit {χ : R ⟶ A} [IsMonHom χ]
    (h : φ ≫ ψ = χ) (P : Mod C R) (V : Mod C A)
    (a : (Mod.extendScalars χ).obj P ⟶ V) :
    (Mod.extendUnit φ P).hom ≫
      ((Mod.extendRestrictAdjunction ψ).homEquiv _ _
        (((Mod.extendScalarsComp φ ψ).inv.app P) ≫
          ((Mod.extendScalarsIsoOfEq h).hom.app P) ≫ a)).hom =
      (Mod.extendUnit χ P).hom ≫ a.hom := by
  simp only [Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom', Mod.comap_map_hom]
  calc
    _ = ((Mod.extendUnit φ P).hom ≫
        (Mod.extendUnit ψ ((Mod.extendScalars φ).obj P)).hom ≫
          ((Mod.extendScalarsComp φ ψ).inv.app P).hom) ≫
            ((Mod.extendScalarsIsoOfEq h).hom.app P).hom ≫ a.hom := by
      simp only [Category.assoc]
    _ = (Mod.extendUnit (φ ≫ ψ) P).hom ≫
        ((Mod.extendScalarsIsoOfEq h).hom.app P).hom ≫ a.hom :=
      congrArg (· ≫ ((Mod.extendScalarsIsoOfEq h).hom.app P).hom ≫ a.hom)
        (scalar_comp_unit φ ψ P)
    _ = _ := by
      rw [← Category.assoc]
      exact congrArg (· ≫ a.hom) (scalar_eq_unit φ ψ h P)

private lemma tensorAdjoint_eq_mixed {χ : R ⟶ A} [IsMonHom χ]
    (h : φ ≫ ψ = χ) (P : Mod C R) (V : Mod C A)
    (a : (Mod.extendScalars χ).obj P ⟶ V) :
    ((Mod.extendRestrictAdjunction ψ).homEquiv _ _
      (((Mod.extendScalarsComp φ ψ).inv.app P) ≫
        ((Mod.extendScalarsIsoOfEq h).hom.app P) ≫ a)).hom =
      (Mod.mixedScalarMap φ χ φ χ ψ h h P).hom ≫ a.hom := by
  let q := (Mod.extendRestrictAdjunction ψ).homEquiv _ _
    (((Mod.extendScalarsComp φ ψ).inv.app P) ≫
      ((Mod.extendScalarsIsoOfEq h).hom.app P) ≫ a)
  let r : (Mod.extendScalars φ).obj P ⟶ (Mod.comap ψ).obj V :=
    (Mod.comapId S).inv.app _ ≫
      Mod.mixedScalarMap φ χ (𝟙 S) ψ ψ h (by simp) P ≫ (Mod.comap ψ).map a
  have hr : (Mod.extendUnit φ P).hom ≫ r.hom =
      (Mod.extendUnit χ P).hom ≫ a.hom := by
    change (Mod.extendUnit φ P).hom ≫
      (𝟙 _ ≫ (Mod.mixedScalarMap φ χ (𝟙 S) ψ ψ h (by simp) P).hom ≫ a.hom) = _
    rw [Category.id_comp, ← Category.assoc]
    exact congrArg (· ≫ a.hom) (mixedScalarMap_unit φ ψ h P)
  have hqr : q = r := by
    apply ((Mod.extendRestrictAdjunction φ).homEquiv P ((Mod.comap ψ).obj V)).injective
    apply Mod.hom_ext
    simp only [Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom', Mod.comap_map_hom]
    exact (tensorAdjoint_unit φ ψ h P V a).trans hr.symm
  calc
    _ = r.hom := congrArg (fun k ↦ k.hom) hqr
    _ = _ := by
      change (𝟙 _ ≫ (Mod.mixedScalarMap φ χ (𝟙 S) ψ ψ h (by simp) P).hom ≫ a.hom) = _
      rw [Category.id_comp]
      rfl

end ScalarUnits

set_option backward.isDefEq.respectTransparency false

section LocalAdjoints

variable (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
  (Y : Scheme.{u}) (g : Y ⟶ X)
  (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    ((upperStar Ab.{u + 1} g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))

/-- The specified finite scalar extension of a local module. -/
noncomputable def finiteCoefficientLocalModel
    (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F) :=
  (Mod.extendScalars ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))).obj P

variable
  (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
  (a : (Mod.extendScalars ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj P ⟶
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)
  (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)

/-- Tensor transitivity followed by the supplied map to the local algebraic-closure module. -/
noncomputable def finiteCoefficientLocalTensorMap :
    (Mod.extendScalars ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F)))).obj
        (finiteCoefficientLocalModel T X f ℓ E Y g P F hEF) ⟶
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M :=
  ((Mod.extendScalarsComp _ _).symm.app P).hom ≫
    ((Mod.extendScalarsIsoOfEq (by
      rw [← Functor.map_comp, ← Functor.map_comp,
        padicSubfieldRingObjMap_comp_toPadicAlgCl])).app P).hom ≫ a

/-- The triangle of pulled coefficient inclusions at a finite stage. -/
theorem finiteCoefficientLocalScalarTriangle :
    (upperStar Ab.{u + 1} g).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)) ≫
      (upperStar Ab.{u + 1} g).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F)) =
    (upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, padicSubfieldRingObjMap_comp_toPadicAlgCl]

/-- The explicit underlying map of the canonical local scalar adjoint. -/
noncomputable def finiteCoefficientLocalAdjointHom :
    (finiteCoefficientLocalModel T X f ℓ E Y g P F hEF).X ⟶
      (((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj
          ((Mod.comap ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M)).X :=
  (Mod.mixedScalarMap
    ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))
    ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))
    ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))
    ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))
    ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F)))
    (finiteCoefficientLocalScalarTriangle T X f ℓ E Y g F hEF)
    (finiteCoefficientLocalScalarTriangle T X f ℓ E Y g F hEF) P).hom ≫ a.hom

set_option backward.isDefEq.respectTransparency false in
private theorem canonicalAdjoint_eq_explicit :
    ((Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ F)))).homEquiv _ _
        (finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF) ≫
    ((upperStar Ab.{u + 1} g).mapModComapIso ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ F))).inv.app M).hom =
      finiteCoefficientLocalAdjointHom T X f ℓ E Y g P M a F hEF := by
  let φ := (upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF))
  let ψ := (upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F))
  let χ := (upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))
  have he : φ ≫ ψ = χ :=
    finiteCoefficientLocalScalarTriangle T X f ℓ E Y g F hEF
  simp only [Mod.comp_hom', Functor.mapModComapIso_inv_app_hom]
  erw [Category.comp_id]
  change ((Mod.extendRestrictAdjunction ψ).homEquiv _ _
    ((Mod.extendScalarsComp φ ψ).inv.app P ≫
      (Mod.extendScalarsIsoOfEq he).hom.app P ≫ a)).hom =
    (Mod.mixedScalarMap φ χ φ χ ψ he he P).hom ≫ a.hom
  exact tensorAdjoint_eq_mixed φ ψ he P _ a

/-- The explicitly constructed local map is linear over the finite coefficient ring. -/
theorem finiteCoefficientLocalAdjointHom_linear :
    γ[
      (upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F)),
      (finiteCoefficientLocalModel T X f ℓ E Y g P F hEF).X] ≫
        finiteCoefficientLocalAdjointHom T X f ℓ E Y g P M a F hEF =
    (upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F)) ◁
      finiteCoefficientLocalAdjointHom T X f ℓ E Y g P M a F hEF ≫
    γ[
      (upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F)),
      (((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj
          ((Mod.comap ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M)).X] := by
  rw [← canonicalAdjoint_eq_explicit]
  exact Mod.act_hom _

/-- The canonical adjoint into the restriction of the given module, at stage `F`. -/
noncomputable def finiteCoefficientLocalAdjoint :
    finiteCoefficientLocalModel T X f ℓ E Y g P F hEF ⟶
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj
          ((Mod.comap ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M) :=
  Mod.Hom.mk' (finiteCoefficientLocalAdjointHom T X f ℓ E Y g P M a F hEF)
    (finiteCoefficientLocalAdjointHom_linear T X f ℓ E Y g P M a F hEF)

/-- The explicit construction is the scalar adjunct of the specified tensor map. -/
theorem finiteCoefficientLocalAdjoint_eq_canonical :
    finiteCoefficientLocalAdjoint T X f ℓ E Y g P M a F hEF =
      (Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ F)))).homEquiv _ _
        (finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF) ≫
    ((upperStar Ab.{u + 1} g).mapModComapIso ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ F))).inv.app M := by
  apply Mod.hom_ext
  exact (canonicalAdjoint_eq_explicit T X f ℓ E Y g P M a F hEF).symm

/-- An invertible original model map remains invertible after tensor transitivity. -/
theorem isIso_finiteCoefficientLocalTensorMap [IsIso a] :
    IsIso (finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF) := by
  unfold finiteCoefficientLocalTensorMap
  infer_instance

/-- A local isomorphism has monic scalar adjoints at every finite stage.
The coefficient-linear projection splits the unit, also after both inverse images. -/
theorem mono_finiteCoefficientLocalAdjoint [IsIso a] :
    Mono (finiteCoefficientLocalAdjoint T X f ℓ E Y g P M a F hEF) := by
  have := mono_pulled_coefficient_unit T X Y f g ℓ F
    (finiteCoefficientLocalModel T X f ℓ E Y g P F hEF)
  have := isIso_finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF
  rw [finiteCoefficientLocalAdjoint_eq_canonical]
  change Mono ((Mod.extendRestrictAdjunction _).homEquiv _ _
    (finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF) ≫ _)
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- Taking the scalar adjunct of the canonical local map recovers its tensor map. -/
theorem finiteCoefficientLocalAdjoint_scalarAdjoint :
    ((Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map
        (padicSubfieldRingObjToPadicAlgCl T ℓ F)))).homEquiv
          (finiteCoefficientLocalModel T X f ℓ E Y g P F hEF)
          (((upperStar Ab.{u + 1} g).mapMod
            ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)).symm
              (finiteCoefficientLocalAdjoint T X f ℓ E Y g P M a F hEF ≫
                ((upperStar Ab.{u + 1} g).mapModComapIso ((upperStar Ab.{u + 1} f).map
                  (padicSubfieldRingObjToPadicAlgCl T ℓ F))).hom.app M) =
      finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF := by
  rw [finiteCoefficientLocalAdjoint_eq_canonical]
  rw [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, Equiv.symm_apply_apply]

end LocalAdjoints
end AlgebraicGeometry.ProEtale
