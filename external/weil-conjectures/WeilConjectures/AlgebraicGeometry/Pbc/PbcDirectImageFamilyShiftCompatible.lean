/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDirectImageStageExact
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.CategoryTheory.StageSystem.CommonStageCalculus
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement

/-! # Exact structures on a normalized direct-image family
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
private theorem pbcAssocWhiskerShift
    {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₁] [Category* D₂] [Category* D₃]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
    [HasShift D₁ ℤ] [HasShift D₂ ℤ] [HasShift D₃ ℤ]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {F' : D₁ ⥤ D₂} {G' : D₂ ⥤ D₃}
    {I : C₁ ⥤ D₁} {J : C₂ ⥤ D₂} {K : C₃ ⥤ D₃}
    [F.CommShift ℤ] [G.CommShift ℤ] [F'.CommShift ℤ] [G'.CommShift ℤ]
    [I.CommShift ℤ] [J.CommShift ℤ] [K.CommShift ℤ]
    (eF : F ⋙ J ≅ I ⋙ F') (eG : G ⋙ K ≅ J ⋙ G')
    [NatTrans.CommShift eF.hom ℤ] [NatTrans.CommShift eG.hom ℤ] :
    let e := Functor.associator F G K ≪≫ Functor.isoWhiskerLeft F eG ≪≫
      (Functor.associator F J G').symm ≪≫ Functor.isoWhiskerRight eF G' ≪≫
      Functor.associator I F' G'
    NatTrans.CommShift e.hom ℤ ∧ NatTrans.CommShift e.inv ℤ := by
  dsimp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv]
  constructor <;> infer_instance

private theorem leftShift_unique
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) (G : D ⥤ C) [G.CommShift ℤ] (adj : F ⊣ G)
    (s : F.CommShift ℤ) (hs : letI := s; adj.CommShift ℤ) :
    s = adj.leftAdjointCommShift ℤ := by
  apply AlgebraicGeometry.Scheme.pbcKanCommShift_ext
  intro n
  apply Adjunction.CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso n)
  · let := s
    have := hs
    intro X
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      (adj.unit_app_commShiftIso_hom_app ℤ n X).symm
  · exact Adjunction.LeftAdjointCommShift.compatibilityUnit_iso adj n

private theorem comparisonShiftOfHEq
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (Φ : A ⥤ C) (Ψ : B ⥤ D) [sΦ : Φ.CommShift ℤ] [sΨ : Ψ.CommShift ℤ]
    {U U' : A ⥤ B} {V V' : C ⥤ D}
    [sU : U.CommShift ℤ] [sU' : U'.CommShift ℤ]
    [sV : V.CommShift ℤ] [sV' : V'.CommShift ℤ]
    (eU : U = U') (eV : V = V') (hU : HEq sU sU') (hV : HEq sV sV')
    (b : Φ ⋙ V ≅ U ⋙ Ψ) (b' : Φ ⋙ V' ≅ U' ⋙ Ψ)
    (hb : ∀ K, HEq (b.hom.app K) (b'.hom.app K))
    (hb' : NatTrans.CommShift b'.hom ℤ) : NatTrans.CommShift b.hom ℤ := by
  subst U'
  subst V'
  cases eq_of_heq hU
  cases eq_of_heq hV
  have he : b.hom = b'.hom := by
    ext K
    exact eq_of_heq (hb K)
  rw [he]
  exact hb'

@[irreducible] private def conjugateIso {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (Φ : A ⥤ C) (Ψ : B ⥤ D) {U U' : A ⥤ B} {V V' : C ⥤ D}
    (eU : U = U') (eV : V = V') (b : Φ ⋙ V' ≅ U' ⋙ Ψ) :
    Φ ⋙ V ≅ U ⋙ Ψ :=
  Functor.isoWhiskerLeft Φ (eqToIso eV) ≪≫ b ≪≫
    Functor.isoWhiskerRight (eqToIso eU).symm Ψ

private theorem conjugateIso_heq {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (Φ : A ⥤ C) (Ψ : B ⥤ D) {U U' : A ⥤ B} {V V' : C ⥤ D}
    (eU : U = U') (eV : V = V') (b : Φ ⋙ V' ≅ U' ⋙ Ψ) (K : A) :
    HEq ((conjugateIso Φ Ψ eU eV b).hom.app K) (b.hom.app K) := by
  subst U'
  subst V'
  unfold conjugateIso
  apply heq_of_eq
  simp

private theorem fullMap_heq
    {A B : Type*} [Category A] [Category B] (P : ObjectProperty A)
    (Q : P.FullSubcategory ⥤ B) {K L K' L' : P.FullSubcategory}
    (hK : K.obj = K'.obj) (hL : L.obj = L'.obj)
    (f : K.obj ⟶ L.obj) (g : K'.obj ⟶ L'.obj) (h : HEq f g) :
    HEq (Q.map (ObjectProperty.homMk f)) (Q.map (ObjectProperty.homMk g)) := by
  have eK : K = K' := by cases K; cases K'; cases hK; rfl
  have eL : L = L' := by cases L; cases L'; cases hL; rfl
  subst K'
  subst L'
  cases eq_of_heq h
  rfl

private theorem unnormalize {C : Type*} [Category C] {A B D E : C}
    (c : A ≅ B) (d : D ≅ E) (β : A ⟶ D) (α : B ⟶ E)
    (h : c.inv ≫ β ≫ d.hom = α) : β = c.hom ≫ α ≫ d.inv := by
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem comparisonShiftOfConjugate
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    {Φ φ : A ⥤ C} {Ψ ψ : B ⥤ D} (U : A ⥤ B) (V : C ⥤ D)
    [sφ : φ.CommShift ℤ] [sψ : ψ.CommShift ℤ] [U.CommShift ℤ] [V.CommShift ℤ]
    (eΦ : Φ = φ) (eΨ : Ψ = ψ) (b : Φ ⋙ V ≅ U ⋙ Ψ)
    (hb : NatTrans.CommShift
      (Functor.isoWhiskerRight (eqToIso eΦ).symm V ≪≫ b ≪≫
        Functor.isoWhiskerLeft U (eqToIso eΨ)).hom ℤ) :
    letI : Φ.CommShift ℤ := eΦ.symm ▸ sφ
    letI : Ψ.CommShift ℤ := eΨ.symm ▸ sψ
    NatTrans.CommShift b.hom ℤ := by
  subst φ
  subst ψ
  simpa using hb

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]

private abbrev canonicalScalarShift {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedExtend φ).CommShift ℤ := by
  let : (pbcDerivedRestrict φ).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.CommShift ℤ)
  exact (pbcDerivedScalarAdjunction φ).leftAdjointCommShift ℤ

private theorem depCongrHEq {A : Sort*} {B : A → Sort*}
    (f : ∀ a, B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientTensor_eq (T : Scheme.{u}) [IsNoetherian T]
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcAmbientScalarExtension l Ω T h =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T := by
  unfold pbcAmbientScalarExtension pbcEmbeddingAmbientTensor
  rw [pbcStageCoefficientMap_eq l Ω T h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientScalarShift_heq (T : Scheme.{u}) [IsNoetherian T]
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    HEq (pbcAmbientScalarCommShift l Ω T h)
      (pbcAmbientScalarShift l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T) := by
  let : (pbcDerivedRestrict (pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T)).CommShift ℤ :=
    inferInstanceAs (((pbcRestrict (pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T)).mapDerivedCategory
      ).CommShift ℤ)
  have hs := scalarAdjunction_shift l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T
  have hc := leftShift_unique _ _
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T))
    (pbcAmbientScalarShift l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T) hs
  have he := depCongrHEq canonicalScalarShift (pbcStageCoefficientMap_eq l Ω T h)
  exact he.trans (heq_of_eq hc.symm)

private theorem actualPushShift_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    pbcActualPushShift f d =
      Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt (pbcActualModulePush f d) := by
  apply (pbcActualPushShift_exists f d).unique
  · exact (pbcActualPushShift_exists f d).exists.choose_spec
  · exact actualRightDerivedUnitShift (pbcActualModulePush f d)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit dX iX dY iY in
private theorem ambientPushShift_exists (f : X ⟶ Y)
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    letI : (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).CommShift ℤ :=
      Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
        (pbcActualModulePush f (pbcStageDatum.{u} l Ω E))
    letI : (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω F)).CommShift ℤ :=
      Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
        (pbcActualModulePush f (pbcStageDatum.{u} l Ω F))
    ∃ b : pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω Y h ≅ pbcAmbientScalarExtension l Ω X h ⋙
          pbcActualDerivedPush f (pbcStageDatum.{u} l Ω F),
      (∀ K, HEq (b.hom.app K)
        ((pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).hom.app K)) ∧
      NatTrans.CommShift b.hom ℤ := by
  have eX : pbcAmbientScalarExtension l Ω X h =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) X := by
    unfold pbcAmbientScalarExtension pbcEmbeddingAmbientTensor
    rw [pbcStageCoefficientMap_eq l Ω X h]
  have eY : pbcAmbientScalarExtension l Ω Y h =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) Y := by
    unfold pbcAmbientScalarExtension pbcEmbeddingAmbientTensor
    rw [pbcStageCoefficientMap_eq l Ω Y h]
  let b := conjugateIso _ _ eX eY
    (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion l Ω h) f)
  have hb := conjugateIso_heq _ _ eX eY
    (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion l Ω h) f)
  refine ⟨b, hb, ?_⟩
  have hraw := (pbcScalarOperations_shift l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).1
  rw [actualPushShift_eq f (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)),
    actualPushShift_eq f (pbcIntegralDatum l (pbcFiniteField.{u} l Ω F))] at hraw
  exact comparisonShiftOfHEq
    (sΦ := Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
      (pbcActualModulePush f (pbcStageDatum.{u} l Ω E)))
    (sΨ := Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
      (pbcActualModulePush f (pbcStageDatum.{u} l Ω F))) _ _ eX eY
    (ambientScalarShift_heq l Ω X h) (ambientScalarShift_heq l Ω Y h) b _ hb
    hraw

private abbrev integralPush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)

private abbrev integralPushShift {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) : (integralPush l Ω f pres E).CommShift ℤ := by
  let : (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).CommShift ℤ :=
    Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
      (pbcActualModulePush f (pbcStageDatum.{u} l Ω E))
  let e : integralPush l Ω f pres E ⋙ pbcStageInclusion l Ω Y E ≅
      pbcStageInclusion l Ω X E ⋙ pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E) :=
    Iso.refl _
  exact Functor.CommShift.ofComp (F := integralPush l Ω f pres E)
    (G := pbcStageInclusion l Ω Y E) e ℤ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralPushShift_exists (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    letI : (integralPush l Ω f pres E).CommShift ℤ := integralPushShift l Ω f pres E
    letI : (integralPush l Ω f pres F).CommShift ℤ := integralPushShift l Ω f pres F
    ∃ b : integralPush l Ω f pres E ⋙ pbcIntegralScalarExtension l Ω Y dY.out iY.out h ≅
        pbcIntegralScalarExtension l Ω X dX.out iX.out h ⋙ integralPush l Ω f pres F,
      (∀ K, HEq (b.hom.app K).hom
        ((pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).hom.app K.obj)) ∧
      NatTrans.CommShift b.hom ℤ := by
  let AE := pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)
  let AF := pbcActualDerivedPush f (pbcStageDatum.{u} l Ω F)
  let : AE.CommShift ℤ := Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
    (pbcActualModulePush f (pbcStageDatum.{u} l Ω E))
  let : AF.CommShift ℤ := Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
    (pbcActualModulePush f (pbcStageDatum.{u} l Ω F))
  let BE := integralPush l Ω f pres E
  let BF := integralPush l Ω f pres F
  let : BE.CommShift ℤ := integralPushShift l Ω f pres E
  let : BF.CommShift ℤ := integralPushShift l Ω f pres F
  let U := pbcAmbientScalarExtension l Ω X h
  let V := pbcAmbientScalarExtension l Ω Y h
  let I := pbcIntegralScalarExtension l Ω X dX.out iX.out h
  let J := pbcIntegralScalarExtension l Ω Y dY.out iY.out h
  obtain ⟨bA, hA, hS⟩ := ambientPushShift_exists l Ω f h
  let b : BE ⋙ J ≅ I ⋙ BF := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ (bA.app K.obj)) (by
      intro K L u
      apply ObjectProperty.hom_ext
      exact bA.hom.naturality u.hom)
  refine ⟨b, (fun K ↦ hA K.obj), ?_⟩
  let eBE : BE ⋙ pbcStageInclusion l Ω Y E ≅ pbcStageInclusion l Ω X E ⋙ AE :=
    Iso.refl _
  let eBF : BF ⋙ pbcStageInclusion l Ω Y F ≅ pbcStageInclusion l Ω X F ⋙ AF :=
    Iso.refl _
  let eI : I ⋙ pbcStageInclusion l Ω X F ≅ pbcStageInclusion l Ω X E ⋙ U :=
    Iso.refl _
  let eJ : J ⋙ pbcStageInclusion l Ω Y F ≅ pbcStageInclusion l Ω Y E ⋙ V :=
    Iso.refl _
  have : NatTrans.CommShift eBE.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := BE)
      (G := pbcStageInclusion l Ω Y E) eBE ℤ
  have : NatTrans.CommShift eBF.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := BF)
      (G := pbcStageInclusion l Ω Y F) eBF ℤ
  have : NatTrans.CommShift eI.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := I)
      (G := pbcStageInclusion l Ω X F) eI ℤ
  have : NatTrans.CommShift eJ.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := J)
      (G := pbcStageInclusion l Ω Y F) eJ ℤ
  let e3 : (I ⋙ BF) ⋙ pbcStageInclusion l Ω Y F ≅
      pbcStageInclusion l Ω X E ⋙ (U ⋙ AF) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft I eBF ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eI AF ≪≫
      Functor.associator _ _ _
  have : NatTrans.CommShift e3.hom ℤ := by
    exact (pbcAssocWhiskerShift eI eBF).1
  have := hS
  apply ScalarLocalization.cscAssocShift eBE eJ e3 b.hom bA.hom
  ext K
  simp only [e3, eBE, eBF, eI, eJ, Iso.refl_hom,
    NatTrans.comp_app, NatTrans.id_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.trans_inv,
    Iso.symm_inv, Iso.refl_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [AF.map_id, Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalBetaShift (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (b : pbcDescentDirectImage l Ω f pres E ⋙
        pbcScalarExtension l Ω Y dY.out iY.out h ≅
      pbcScalarExtension l Ω X dX.out iX.out h ⋙ pbcDescentDirectImage l Ω f pres F)
    (hb : ∀ K : pbcIntegralStage l Ω X E,
      HEq ((pbcScalarIntegralComparison l Ω Y dY.out iY.out h).inv.app
          ((integralPush l Ω f pres E).obj K) ≫ b.hom.app (ScalarLocalization.mk K) ≫
        (pbcDescentDirectImage l Ω f pres F).map
          ((pbcScalarIntegralComparison l Ω X dX.out iX.out h).hom.app K))
        ((pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f
          dX.out dY.out iX.out iY.out (pres E) (pres F)).exists.choose.hom.app
            (ScalarLocalization.mk K))) :
    letI := pbcDirectImageStageCommShift l Ω f pres E
    letI := pbcDirectImageStageCommShift l Ω f pres F
    NatTrans.CommShift b.hom ℤ := by
  let BE := integralPush l Ω f pres E
  let BF := integralPush l Ω f pres F
  let : BE.CommShift ℤ := integralPushShift l Ω f pres E
  let : BF.CommShift ℤ := integralPushShift l Ω f pres F
  let RE := pbcDescentDirectImage l Ω f pres E
  let RF := pbcDescentDirectImage l Ω f pres F
  let : RE.CommShift ℤ := pbcDirectImageStageCommShift l Ω f pres E
  let : RF.CommShift ℤ := pbcDirectImageStageCommShift l Ω f pres F
  let QXE := pbcStageLocalization l Ω X E
  let QYE := pbcStageLocalization l Ω Y E
  let QXF := pbcStageLocalization l Ω X F
  let QYF := pbcStageLocalization l Ω Y F
  let I := pbcIntegralScalarExtension l Ω X dX.out iX.out h
  let J := pbcIntegralScalarExtension l Ω Y dY.out iY.out h
  let TX := pbcScalarExtension l Ω X dX.out iX.out h
  let TY := pbcScalarExtension l Ω Y dY.out iY.out h
  obtain ⟨bI, hI, sI⟩ := integralPushShift_exists l Ω f pres h
  have := sI
  let eE : QXE ⋙ RE ≅ BE ⋙ QYE := Iso.refl _
  let eF : QXF ⋙ RF ≅ BF ⋙ QYF := Iso.refl _
  let eX : QXE ⋙ TX ≅ I ⋙ QXF := pbcScalarIntegralComparison l Ω X dX.out iX.out h
  let eY : QYE ⋙ TY ≅ J ⋙ QYF := pbcScalarIntegralComparison l Ω Y dY.out iY.out h
  have : NatTrans.CommShift eE.hom ℤ :=
    (pbcDirectImageStageShift_exists l Ω f pres E).exists.choose_spec.2
  have : NatTrans.CommShift eF.hom ℤ :=
    (pbcDirectImageStageShift_exists l Ω f pres F).exists.choose_spec.2
  have : NatTrans.CommShift eX.hom ℤ :=
    (pbcScalarShift_exists l Ω X dX.out iX.out h).exists.choose_spec
  have : NatTrans.CommShift eY.hom ℤ :=
    (pbcScalarShift_exists l Ω Y dY.out iY.out h).exists.choose_spec
  let e3 : QXE ⋙ (TX ⋙ RF) ≅ (I ⋙ BF) ⋙ QYF :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eX RF ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft I eF ≪≫
      (Functor.associator _ _ _).symm
  have : NatTrans.CommShift e3.hom ℤ := by
    simpa only [e3, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Category.assoc] using
      (pbcAssocWhiskerShift eX.symm eF.symm).2
  apply ScalarLocalization.cscAssocShiftOfWhiskerLeft eE eY e3 bI.hom b.hom
  · intro K
    have hr := (pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f
      dX.out dY.out iX.out iY.out (pres E) (pres F)).exists.choose_spec
        (ScalarLocalization.mk K)
    have hm : HEq (QYF.map (bI.hom.app K))
        ((pbcStageLocalization l Ω Y F).map (ObjectProperty.homMk
          (X := (pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) Y
            dY.out iY.out).obj (BE.obj K))
          (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω F)
            (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω F)) (pres F)).obj
              ((pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E)
                (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) X
                dX.out iX.out).obj K))
          ((pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).hom.app
              K.obj))) := by
      apply fullMap_heq _ _ ?_ ?_ _ _ (hI K)
      · exact congrArg (fun A ↦ A.obj ((BE.obj K).obj)) (ambientTensor_eq l Ω Y h)
      · exact congrArg (fun A ↦
          (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω F)).obj (A.obj K.obj))
          (ambientTensor_eq l Ω X h)
    have hn := eq_of_heq ((hb K).trans (hr.trans hm.symm))
    have hc := unnormalize (eY.app (BE.obj K)) (RF.mapIso (eX.app K))
      (b.hom.app (QXE.obj K)) (QYF.map (bI.hom.app K)) hn
    simp only [eE, e3, eF, Iso.refl_hom, Iso.refl_inv, Iso.trans_inv, Iso.symm_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app, NatTrans.id_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    erw [Category.id_comp]
    exact hc
  · intro K
    exact ⟨K.obj, 𝟙 _, by infer_instance⟩

/-- Transport the uniquely normalized actual stage shifts along the endpoint
identifications. -/
@[instance_reducible] def pbcDirectImageFamilyCommShift (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (R : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out))
    (hR : ∀ E : Padic.FiniteCoefficientFields l Ω,
      R.Φ E = pbcDescentDirectImage l Ω f pres E) :
    ∀ E : Padic.FiniteCoefficientFields l Ω, (R.Φ E).CommShift ℤ :=
  fun E ↦ (hR E).symm ▸ pbcDirectImageStageCommShift l Ω f pres E

/-- Normalized direct-image scalar comparisons commute with the fixed stage shifts.
This asserts only the comparison equation; it constructs no stage functor,
coherent family, or exact structure. -/
theorem pbcDirectImageFamilyShiftCompatible (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (R : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out))
    (hR : ∀ E : Padic.FiniteCoefficientFields l Ω,
      R.Φ E = pbcDescentDirectImage l Ω f pres E)
    (bR : PbcDirectImageBetaSpec l Ω f pres R) :
    letI : ∀ E : Padic.FiniteCoefficientFields l Ω, (R.Φ E).CommShift ℤ :=
      pbcDirectImageFamilyCommShift l Ω f pres R hR
    ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F),
      NatTrans.CommShift (R.β h).hom ℤ := by
  let : ∀ E : Padic.FiniteCoefficientFields l Ω, (R.Φ E).CommShift ℤ :=
    pbcDirectImageFamilyCommShift l Ω f pres R hR
  intro E F h
  let : (pbcDescentDirectImage l Ω f pres E).CommShift ℤ :=
    pbcDirectImageStageCommShift l Ω f pres E
  let : (pbcDescentDirectImage l Ω f pres F).CommShift ℤ :=
    pbcDirectImageStageCommShift l Ω f pres F
  apply comparisonShiftOfConjugate
    (sφ := pbcDirectImageStageCommShift l Ω f pres E)
    (sψ := pbcDirectImageStageCommShift l Ω f pres F)
    _ _ (hR E) (hR F) (R.β h)
  apply rationalBetaShift l Ω f pres h
  intro K
  exact bR h (hR E) (hR F) K

end AlgebraicGeometry.Scheme
