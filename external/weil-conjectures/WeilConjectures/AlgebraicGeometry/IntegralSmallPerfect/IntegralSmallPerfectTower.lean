/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Module.Shrink
import Mathlib.RingTheory.Finiteness.Small
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral

/-! # Descending perfect coefficient towers to the scalar universe

## References

* Stacks Tags 064Z and 09C6
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.ProEtale.IntegralSmallPerfect

instance bigModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory (ModuleCat.{u + 1} A) := HasDerivedCategory.standard _

private def liftComplex
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (K : CochainComplex D ℤ) (X : ℤ → C) (e : ∀ i, F.obj (X i) ≅ K.X i) :
    CochainComplex C ℤ where
  X := X
  d i j := F.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv)
  shape i j hij := by
    apply F.map_injective
    simp [K.shape i j hij]
  d_comp_d' i j k _ _ := by
    apply F.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero]
    simp [Category.assoc]

private def liftComplexIso
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (K : CochainComplex D ℤ) (X : ℤ → C) (e : ∀ i, F.obj (X i) ≅ K.X i) :
    (F.mapHomologicalComplex (.up ℤ)).obj (liftComplex F K X e) ≅ K := by
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j _
  simp [liftComplex, Category.assoc]

private theorem perfect_derived_map_bijective
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P L : CochainComplex C ℤ) [P.IsKProjective]
    [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj P)] :
    Function.Bijective
      (F.mapDerivedCategory.map :
        (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) → _) := by
  let qC := HomotopyCategory.quotient C (.up ℤ)
  let qD := HomotopyCategory.quotient D (.up ℤ)
  let FH := F.mapHomotopyCategory (.up ℤ)
  let E := F.mapDerivedCategoryFactorsh
  have hP := CochainComplex.IsKProjective.Qh_map_bijective P (qC.obj L)
  let eP := (DerivedCategory.quotientCompQhIso C).app P
  let eL := (DerivedCategory.quotientCompQhIso C).app L
  have hFP : CochainComplex.IsKProjective
      ((F.mapHomologicalComplex (.up ℤ)).obj P) := inferInstance
  let eHP := (F.mapHomotopyCategoryFactors (.up ℤ)).app P
  let eHL := (F.mapHomotopyCategoryFactors (.up ℤ)).app L
  have hQD : Function.Bijective
      (DerivedCategory.Qh.map : (FH.obj (qC.obj P) ⟶ FH.obj (qC.obj L)) → _) := by
    have h := CochainComplex.IsKProjective.Qh_map_bijective
      ((F.mapHomologicalComplex (.up ℤ)).obj P) (FH.obj (qC.obj L))
    have h' := h.comp (Iso.homCongr eHP (Iso.refl _)).bijective
    have h'' := (Iso.homCongr (DerivedCategory.Qh.mapIso eHP).symm
      (Iso.refl _)).bijective.comp h'
    simpa [FH, qC, Function.comp_def, Iso.homCongr, ← Functor.map_comp, Category.assoc]
      using h''
  have hFH : Function.Bijective (FH.map : (qC.obj P ⟶ qC.obj L) → _) :=
    ⟨FH.map_injective, FH.map_surjective⟩
  have hB := hQD.comp hFH
  have hE := (Iso.homCongr (E.app (qC.obj P)).symm
    (E.app (qC.obj L)).symm).bijective.comp hB
  have hcomm : (fun f : qC.obj P ⟶ qC.obj L ↦
      (E.app (qC.obj P)).hom ≫ DerivedCategory.Qh.map (FH.map f) ≫
        (E.app (qC.obj L)).inv) =
      fun f ↦ F.mapDerivedCategory.map (DerivedCategory.Qh.map f) := by
    funext f
    have hn := E.hom.naturality f
    dsimp only [Functor.comp_map] at hn
    change E.hom.app (qC.obj P) ≫ DerivedCategory.Qh.map (FH.map f) ≫
      E.inv.app (qC.obj L) = _
    rw [← reassoc_of% hn]
    simp
  change Function.Bijective (fun f : qC.obj P ⟶ qC.obj L ↦
      (E.app (qC.obj P)).hom ≫ DerivedCategory.Qh.map (FH.map f) ≫
        (E.app (qC.obj L)).inv) at hE
  rw [hcomm] at hE
  have hM : Function.Bijective (F.mapDerivedCategory.map :
      (DerivedCategory.Qh.obj (qC.obj P) ⟶ DerivedCategory.Qh.obj (qC.obj L)) → _) :=
    (Function.Bijective.of_comp_iff _ hP).mp hE
  have h' := hM.comp (Iso.homCongr eP.symm eL.symm).bijective
  have h'' := (Iso.homCongr (F.mapDerivedCategory.mapIso eP)
    (F.mapDerivedCategory.mapIso eL)).bijective.comp h'
  simpa only [Function.comp_def, Iso.homCongr_apply, Functor.map_comp, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_map_assoc, Iso.inv_hom_id_map, Category.comp_id] using h''


private theorem shrink_finite_projective_complex
    (A : Type u) [CommRing A] (P : CochainComplex (ModuleCat.{v} A) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hp : ∀ i : ℤ, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) :
    ∃ (Q : CochainComplex (ModuleCat.{u} A) ℤ),
      Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Projective A (Q.X i) ∧ Module.Finite A (Q.X i)) ∧
      Nonempty (((ModuleCat.uliftFunctor.{max u v, u} A).mapHomologicalComplex
        (.up ℤ)).obj Q ≅
        ((ModuleCat.uliftFunctor.{u, v} A).mapHomologicalComplex (.up ℤ)).obj P) := by
  let F := ModuleCat.uliftFunctor.{max u v, u} A
  let G := ModuleCat.uliftFunctor.{u, v} A
  let (i : ℤ) : Module.Finite A (P.X i) := (hp i).2
  let (i : ℤ) : Module.Projective A (P.X i) := (hp i).1
  let (i : ℤ) : Small.{u} (P.X i) := Module.Finite.small A (P.X i)
  let X (i : ℤ) := ModuleCat.of A (Shrink.{u} (P.X i))
  let e (i : ℤ) : F.obj (X i) ≅ (G.obj (P.X i)) :=
    ((ULift.moduleEquiv : ULift.{max u v} (Shrink.{u} (P.X i)) ≃ₗ[A]
      Shrink.{u} (P.X i)).trans ((Shrink.linearEquiv A (P.X i)).trans
        (ULift.moduleEquiv : ULift.{u} (P.X i) ≃ₗ[A] P.X i).symm)).toModuleIso
  let Q := liftComplex F ((G.mapHomologicalComplex (.up ℤ)).obj P) X e
  let eQ := liftComplexIso F ((G.mapHomologicalComplex (.up ℤ)).obj P) X e
  let : P.IsStrictlyGE a := ha
  let : P.IsStrictlyLE b := hb
  refine ⟨Q, ?_, ?_, ?_, ⟨eQ⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    apply IsZero.of_full_of_faithful_of_isZero F (Q.X i)
    exact ((G.map_isZero (P.isZero_of_isStrictlyGE a i hi))).of_iso (e i)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    apply IsZero.of_full_of_faithful_of_isZero F (Q.X i)
    exact ((G.map_isZero (P.isZero_of_isStrictlyLE b i hi))).of_iso (e i)
  · intro i
    change Module.Projective A (Shrink.{u} (P.X i)) ∧
      Module.Finite A (Shrink.{u} (P.X i))
    exact ⟨inferInstance, Module.Finite.of_surjective
      (Shrink.linearEquiv A (P.X i)).symm.toLinearMap
      (Shrink.linearEquiv A (P.X i)).symm.surjective⟩

attribute [local instance] RingHomInvPair.of_ringEquiv in
private theorem finite_projective_restrict_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (M : ModuleCat.{v} B) (hP : Module.Projective B M) (hF : Module.Finite B M) :
    Module.Projective A ((ModuleCat.restrictScalars e.toRingHom).obj M) ∧
      Module.Finite A ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  let j : M ≃ₛₗ[e.symm.toRingHom] N :=
    { Equiv.refl _ with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change a • x = e (e.symm a) • x
        rw [e.apply_symm_apply] }
  let : Module.Projective B M := hP
  let : Module.Finite B M := hF
  exact ⟨Module.Projective.of_equiv (σ' := e.toRingHom) j,
    Module.Finite.of_surjective j.toLinearMap j.surjective⟩

private def uliftSameIso (A : Type u) [CommRing A] :
    ModuleCat.uliftFunctor.{u, u + 1} A ≅ 𝟭 (ModuleCat.{u + 1} A) := by
  refine NatIso.ofComponents (fun M ↦
    (ULift.moduleEquiv : ULift.{u} M ≃ₗ[A] M).toModuleIso) ?_
  intro M N f
  ext x
  rfl

instance (priority := 10000) liftedRestrictEquivalence
    (A : Type u) [CommRing A] :
    (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u + 1, u + 1}
    (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm).isEquivalence_functor

instance (priority := 100000) liftedRestrictLeftAdjoint
    (A : Type u) [CommRing A] :
    (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom).IsLeftAdjoint :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u + 1, u + 1}
    (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm).toAdjunction.isLeftAdjoint

instance (priority := 100000) liftedRestrictRightAdjoint
    (A : Type u) [CommRing A] :
    (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom).IsRightAdjoint :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u + 1, u + 1}
    (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm).symm.toAdjunction.isRightAdjoint

private theorem small_perfect_of_lifted_perfect
    (A : Type u) [CommRing A]
    (M : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (hM : DerivedCategory.IsPerfect M) :
    ∃ N : DerivedCategory (ModuleCat.{u} A),
      DerivedCategory.IsPerfectRingComplex N ∧
      Nonempty
        ((ModuleCat.uliftFunctor.{u + 1, u} A).mapDerivedCategory.obj N ≅
          (ModuleCat.restrictScalars.{u + 1}
            (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom).mapDerivedCategory.obj
              M) := by
  obtain ⟨P, a, b, ha, hb, hp, ⟨eP⟩⟩ := hM
  let e := (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm
  let R := ModuleCat.restrictScalars.{u + 1} e.toRingHom
  let P' := (R.mapHomologicalComplex (.up ℤ)).obj P
  have hp' (i : ℤ) : Module.Projective A (P'.X i) ∧ Module.Finite A (P'.X i) :=
    finite_projective_restrict_ringEquiv e (P.X i) (hp i).1 (hp i).2
  let : P.IsStrictlyGE a := ha
  let : P.IsStrictlyLE b := hb
  have ha' : CochainComplex.IsStrictlyGE P' a := inferInstance
  have hb' : CochainComplex.IsStrictlyLE P' b := inferInstance
  obtain ⟨Q, hQa, hQb, hQ, ⟨eQ⟩⟩ :=
    shrink_finite_projective_complex A P' a b ha' hb' hp'
  let F := ModuleCat.uliftFunctor.{u + 1, u} A
  let eC : (F.mapHomologicalComplex (.up ℤ)).obj Q ≅ P' :=
    eQ ≪≫ (NatIso.mapHomologicalComplex (uliftSameIso A) (.up ℤ)).app P'
  refine ⟨DerivedCategory.Q.obj Q, ⟨Q, a, b, hQa, hQb, hQ, ⟨Iso.refl _⟩⟩, ?_⟩
  exact ⟨F.mapDerivedCategoryFactors.app Q ≪≫ DerivedCategory.Q.mapIso eC ≪≫
    (R.mapDerivedCategoryFactors.app P).symm ≪≫ R.mapDerivedCategory.mapIso eP.symm⟩


private theorem universal_arrow_descend
    {C₀ D₀ C₁ D₁ : Type*}
    [Category* C₀] [Category* D₀] [Category* C₁] [Category* D₁]
    (U₀ : D₀ ⥤ C₀) (U₁ : D₁ ⥤ C₁) (F : C₀ ⥤ C₁) (G : D₀ ⥤ D₁)
    (e : U₀ ⋙ F ≅ G ⋙ U₁) (X : C₀) (Y : D₀)
    (η : X ⟶ U₀.obj Y)
    (hF : ∀ Z : D₀, Function.Bijective
      (F.map : (X ⟶ U₀.obj Z) → _))
    (hG : ∀ Z : D₀, Function.Bijective (G.map : (Y ⟶ Z) → _))
    (hη : ∀ Z : D₀, Function.Bijective fun g : G.obj Y ⟶ G.obj Z ↦
      (F.map η ≫ (e.app Y).hom) ≫ U₁.map g) :
    ∀ Z : D₀, Function.Bijective fun g : Y ⟶ Z ↦ η ≫ U₀.map g := by
  intro Z
  have hb := (hη Z).comp (hG Z)
  have hc := (Iso.homCongr (Iso.refl (F.obj X)) (e.app Z).symm).bijective.comp hb
  have heq : (fun g : Y ⟶ Z ↦
      ((F.map η ≫ (e.app Y).hom) ≫ U₁.map (G.map g)) ≫ (e.app Z).inv) =
      fun g : Y ⟶ Z ↦ F.map (η ≫ U₀.map g) := by
    funext g
    rw [Functor.map_comp]
    have hn := e.hom.naturality g
    dsimp only [Functor.comp_map] at hn
    change ((F.map η ≫ e.hom.app Y) ≫ U₁.map (G.map g)) ≫ e.inv.app Z = _
    simp only [Category.assoc]
    rw [← reassoc_of% hn]
    simp
  have hc' : Function.Bijective (fun g : Y ⟶ Z ↦
      ((F.map η ≫ (e.app Y).hom) ≫ U₁.map (G.map g)) ≫ (e.app Z).inv) := by
    simpa only [Function.comp_def, Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom,
      Category.id_comp] using hc
  rw [heq] at hc'
  exact (Function.Bijective.of_comp_iff' (hF Z) _).mp hc'

private theorem map_bijective_of_isos
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {K K' L L' : C} (e : K ≅ K') (d : L ≅ L')
    (hF : Function.Bijective (F.map : (K' ⟶ L') → _)) :
    Function.Bijective (F.map : (K ⟶ L) → _) := by
  constructor
  · intro f g h
    apply (Iso.homCongr e d).injective
    apply hF.injective
    simp only [Iso.homCongr_apply, Functor.map_comp, h]
  · intro f
    obtain ⟨g, hg⟩ := hF.surjective (F.map e.inv ≫ f ≫ F.map d.hom)
    refine ⟨e.hom ≫ g ≫ d.inv, ?_⟩
    simp only [Functor.map_comp, hg]
    simp [Category.assoc]

private theorem ulift_perfect_map_bijective
    (A : Type u) [CommRing A]
    (M N : DerivedCategory (ModuleCat.{u} A))
    (hM : DerivedCategory.IsPerfectRingComplex M) :
    Function.Bijective ((ModuleCat.uliftFunctor.{u + 1, u} A).mapDerivedCategory.map :
      (M ⟶ N) → _) := by
  let F := ModuleCat.uliftFunctor.{u + 1, u} A
  obtain ⟨P, a, b, ha, hb, hP, ⟨eP⟩⟩ := hM
  let L := DerivedCategory.Q.objPreimage N
  let eL : DerivedCategory.Q.obj L ≅ N := DerivedCategory.Q.objObjPreimageIso N
  let : P.IsStrictlyLE b := hb
  let (i : ℤ) : Module.Projective A (P.X i) := (hP i).1
  let (i : ℤ) : Projective (P.X i) := inferInstance
  let : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  let (i : ℤ) : Projective (((F.mapHomologicalComplex (.up ℤ)).obj P).X i) :=
    Functor.projective_obj F (P.X i)
  let : CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    CochainComplex.isKProjective_of_projective _ b
  exact map_bijective_of_isos F.mapDerivedCategory eP eL.symm
    (perfect_derived_map_bijective F P L)

private def uliftRestrictIso {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) :
    ModuleCat.restrictScalars.{u} q ⋙ ModuleCat.uliftFunctor.{u + 1, u} A ≅
      ModuleCat.uliftFunctor.{u + 1, u} B ⋙ ModuleCat.restrictScalars.{u + 1} q := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact (LinearEquiv.refl A _).toModuleIso
  · intro M N f
    ext x
    rfl


private theorem exists_universal_arrow_descend
    {C₀ D₀ C₁ D₁ : Type*}
    [Category* C₀] [Category* D₀] [Category* C₁] [Category* D₁]
    (U₀ : D₀ ⥤ C₀) (U₁ : D₁ ⥤ C₁) (F : C₀ ⥤ C₁) (G : D₀ ⥤ D₁)
    (e : U₀ ⋙ F ≅ G ⋙ U₁) (X : C₀) (Y : D₀)
    (η₁ : F.obj X ⟶ U₁.obj (G.obj Y))
    (hF : ∀ Z : D₀, Function.Bijective
      (F.map : (X ⟶ U₀.obj Z) → _))
    (hG : ∀ Z : D₀, Function.Bijective (G.map : (Y ⟶ Z) → _))
    (hη₁ : ∀ Z : D₁, Function.Bijective fun g : G.obj Y ⟶ Z ↦ η₁ ≫ U₁.map g) :
    ∃ η₀ : X ⟶ U₀.obj Y,
      (∀ Z : D₀, Function.Bijective fun g : Y ⟶ Z ↦ η₀ ≫ U₀.map g) ∧
      F.map η₀ ≫ (e.app Y).hom = η₁ := by
  obtain ⟨η₀, hη₀⟩ := (hF Y).surjective (η₁ ≫ (e.app Y).inv)
  have hc : F.map η₀ ≫ (e.app Y).hom = η₁ := by rw [hη₀]; simp
  refine ⟨η₀, universal_arrow_descend U₀ U₁ F G e X Y η₀ hF hG ?_, hc⟩
  intro Z
  rw [hc]
  exact hη₁ (G.obj Z)

private theorem universal_arrow_map
    {C₀ D₀ C₁ D₁ : Type*}
    [Category* C₀] [Category* D₀] [Category* C₁] [Category* D₁]
    (U₀ : D₀ ⥤ C₀) (U₁ : D₁ ⥤ C₁) (F : C₀ ⥤ C₁) (G : D₀ ⥤ D₁)
    [F.Full] [F.Faithful] [G.Full] [G.Faithful] [G.EssSurj]
    (e : U₀ ⋙ F ≅ G ⋙ U₁) (X : C₀) (Y : D₀)
    (η : X ⟶ U₀.obj Y)
    (hη : ∀ Z : D₀, Function.Bijective fun g : Y ⟶ Z ↦ η ≫ U₀.map g) :
    ∀ Z : D₁, Function.Bijective fun g : G.obj Y ⟶ Z ↦
      (F.map η ≫ (e.app Y).hom) ≫ U₁.map g := by
  intro Z
  let Z₀ := G.objPreimage Z
  let d : G.obj Z₀ ≅ Z := G.objObjPreimageIso Z
  have h₀ : Function.Bijective (fun g : Y ⟶ Z₀ ↦
      F.map (η ≫ U₀.map g) ≫ (e.app Z₀).hom) :=
    ((e.app Z₀).homToEquiv (Z := F.obj X)).bijective.comp
      ((show Function.Bijective (F.map : (X ⟶ U₀.obj Z₀) → _) from
        ⟨F.map_injective, F.map_surjective⟩).comp (hη Z₀))
  have hEq : (fun g : Y ⟶ Z₀ ↦ F.map (η ≫ U₀.map g) ≫ (e.app Z₀).hom) =
      fun g ↦ (F.map η ≫ (e.app Y).hom) ≫ U₁.map (G.map g) := by
    funext g
    have hn := e.hom.naturality g
    dsimp only [Functor.comp_map] at hn
    simp only [Functor.map_comp, Category.assoc]
    change F.map η ≫ F.map (U₀.map g) ≫ e.hom.app Z₀ =
      F.map η ≫ e.hom.app Y ≫ U₁.map (G.map g)
    rw [hn]
  rw [hEq] at h₀
  have hb : Function.Bijective (fun g : G.obj Y ⟶ G.obj Z₀ ↦
      (F.map η ≫ (e.app Y).hom) ≫ U₁.map g) :=
    (Function.Bijective.of_comp_iff _
      (show Function.Bijective (G.map : (Y ⟶ Z₀) → _) from
        ⟨G.map_injective, G.map_surjective⟩)).mp h₀
  have hc := ((U₁.mapIso d).homToEquiv (Z := F.obj X)).bijective.comp hb
  have hd := hc.comp (d.symm.homToEquiv (Z := G.obj Y)).bijective
  simpa [Function.comp_def, ← Functor.map_comp, Category.assoc] using hd

private theorem universal_arrow_of_isos
    {C D : Type*} [Category* C] [Category* D]
    (U : D ⥤ C) {X X' : C} {Y Y' : D}
    (η : X' ⟶ U.obj Y')
    (hη : ∀ Z : D, Function.Bijective fun g : Y' ⟶ Z ↦ η ≫ U.map g)
    (e : X ≅ X') (d : Y ≅ Y') :
    ∀ Z : D, Function.Bijective fun g : Y ⟶ Z ↦
      (e.hom ≫ η ≫ U.map d.inv) ≫ U.map g := by
  intro Z
  have h := (e.symm.homFromEquiv (Z := U.obj Z)).bijective.comp
    ((hη Z).comp (d.homFromEquiv (Z := Z)).bijective)
  simpa only [Function.comp_def, Iso.homFromEquiv_apply, Iso.symm_inv,
    Functor.map_comp, Category.assoc] using h

/-- The actual scalar homomorphism on the lifted rings. -/
def uliftRingMap {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) :
    ULift.{u + 1} A →+* ULift.{u + 1} B :=
  ULift.ringEquiv.symm.toRingHom.comp (q.comp ULift.ringEquiv.toRingHom)

private instance (priority := 100000) liftedMapRestrictLeftAdjoint
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) :
    (ModuleCat.restrictScalars.{u + 1} (uliftRingMap q)).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
    (uliftRingMap q)).isLeftAdjoint

private instance (priority := 100000) liftedMapRestrictRightAdjoint
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) :
    (ModuleCat.restrictScalars.{u + 1} (uliftRingMap q)).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (uliftRingMap q)).isRightAdjoint

private instance (priority := 100000) bigMapRestrictLeftAdjoint
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) :
    (ModuleCat.restrictScalars.{u + 1} q).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u, u} q).isLeftAdjoint

private instance (priority := 100000) bigMapRestrictRightAdjoint
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) :
    (ModuleCat.restrictScalars.{u + 1} q).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} q).isRightAdjoint

private def ringRestrictSquare {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) :
    ModuleCat.restrictScalars.{u + 1} (uliftRingMap q) ⋙
      ModuleCat.restrictScalars.{u + 1}
        (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom ≅
    ModuleCat.restrictScalars.{u + 1}
        (ULift.ringEquiv : ULift.{u + 1} B ≃+* B).symm.toRingHom ⋙
      ModuleCat.restrictScalars.{u + 1} q := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact (show
        ((ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom).obj
          ((ModuleCat.restrictScalars.{u + 1} (uliftRingMap q)).obj M)) ≃ₗ[A]
        ((ModuleCat.restrictScalars.{u + 1} q).obj
          ((ModuleCat.restrictScalars.{u + 1}
            (ULift.ringEquiv : ULift.{u + 1} B ≃+* B).symm.toRingHom).obj M)) from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }).toModuleIso
  · intro M N f
    ext x
    rfl

private theorem small_universal_arrow
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B)
    (S : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (T : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} B)))
    (M : DerivedCategory (ModuleCat.{u} A))
    (N : DerivedCategory (ModuleCat.{u} B))
    (hM : DerivedCategory.IsPerfectRingComplex M)
    (hN : DerivedCategory.IsPerfectRingComplex N)
    (eM : (ModuleCat.uliftFunctor.{u + 1, u} A).mapDerivedCategory.obj M ≅
      (ModuleCat.restrictScalars.{u + 1}
        (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom).mapDerivedCategory.obj S)
    (eN : (ModuleCat.uliftFunctor.{u + 1, u} B).mapDerivedCategory.obj N ≅
      (ModuleCat.restrictScalars.{u + 1}
        (ULift.ringEquiv : ULift.{u + 1} B ≃+* B).symm.toRingHom).mapDerivedCategory.obj T)
    (η : S ⟶ (ModuleCat.restrictScalars.{u + 1} (uliftRingMap q)).mapDerivedCategory.obj T)
    (hη : ∀ Z : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} B)),
      Function.Bijective fun g : T ⟶ Z ↦
        η ≫ (ModuleCat.restrictScalars.{u + 1} (uliftRingMap q)).mapDerivedCategory.map g) :
    ∃ ξ : M ⟶ (ModuleCat.restrictScalars.{u} q).mapDerivedCategory.obj N,
      ∀ Z : DerivedCategory (ModuleCat.{u} B), Function.Bijective fun g : N ⟶ Z ↦
        ξ ≫ (ModuleCat.restrictScalars.{u} q).mapDerivedCategory.map g := by
  let RA := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom
  let RB := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : ULift.{u + 1} B ≃+* B).symm.toRingHom
  let U := (ModuleCat.restrictScalars.{u + 1} (uliftRingMap q)).mapDerivedCategory
  let V := (ModuleCat.restrictScalars.{u + 1} q).mapDerivedCategory
  let F := RA.mapDerivedCategory
  let G := RB.mapDerivedCategory
  let d : U ⋙ F ≅ G ⋙ V := Functor.mapDerivedCategorySquareIso (ringRestrictSquare q)
  let η' : F.obj S ⟶ V.obj (G.obj T) := F.map η ≫ (d.app T).hom
  have hη' := universal_arrow_map U V F G d S T η hη
  let FM := (ModuleCat.uliftFunctor.{u + 1, u} A).mapDerivedCategory
  let GN := (ModuleCat.uliftFunctor.{u + 1, u} B).mapDerivedCategory
  let η'' : FM.obj M ⟶ V.obj (GN.obj N) := eM.hom ≫ η' ≫ V.map eN.inv
  have hη'' := universal_arrow_of_isos V η' hη' eM eN
  let c : (ModuleCat.restrictScalars.{u} q).mapDerivedCategory ⋙ FM ≅ GN ⋙ V :=
    Functor.mapDerivedCategorySquareIso (uliftRestrictIso q)
  obtain ⟨ξ, hξ, _⟩ := exists_universal_arrow_descend
    (ModuleCat.restrictScalars.{u} q).mapDerivedCategory V FM GN c M N η''
    (fun Z ↦ ulift_perfect_map_bijective A M _ hM)
    (fun Z ↦ ulift_perfect_map_bijective B N Z hN) hη''
  exact ⟨ξ, hξ⟩

/-- Perfect coefficient levels and their universal quotient arrows descend to small modules. -/
theorem smallPerfect_tower
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (q : ∀ n, A (n + 1) →+* A n)
    (S : ∀ n, DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (A n))))
    (hS : ∀ n, DerivedCategory.IsPerfect (S n))
    (β : ∀ n, Nonempty
      ((ConstantScalarRealization.moduleDerivedExtension (uliftRingMap (q n))).obj
        (S (n + 1)) ≅ S n)) :
    ∃ M : ∀ n, DerivedCategory (ModuleCat.{u} (A n)),
      (∀ n, DerivedCategory.IsPerfectRingComplex (M n)) ∧
      (∀ n, Nonempty
        ((ModuleCat.uliftFunctor.{u + 1, u} (A n)).mapDerivedCategory.obj (M n) ≅
          (ModuleCat.restrictScalars.{u + 1}
            (ULift.ringEquiv : ULift.{u + 1} (A n) ≃+* A n).symm.toRingHom).mapDerivedCategory.obj
              (S n))) ∧
      ∃ f : ∀ n, M (n + 1) ⟶
          (ModuleCat.restrictScalars.{u} (q n)).mapDerivedCategory.obj (M n),
        ∀ n (N : DerivedCategory (ModuleCat.{u} (A n))),
          Function.Bijective fun g : M n ⟶ N ↦
            f n ≫ (ModuleCat.restrictScalars.{u} (q n)).mapDerivedCategory.map g := by
  classical
  choose M hM eM using fun n ↦ small_perfect_of_lifted_perfect (A n) (S n) (hS n)
  have hf (n : ℕ) : ∃ f : M (n + 1) ⟶
      (ModuleCat.restrictScalars.{u} (q n)).mapDerivedCategory.obj (M n),
      ∀ N : DerivedCategory (ModuleCat.{u} (A n)), Function.Bijective fun g : M n ⟶ N ↦
        f ≫ (ModuleCat.restrictScalars.{u} (q n)).mapDerivedCategory.map g := by
    obtain ⟨e⟩ := β n
    let adj := ConstantScalarRealization.moduleDerivedAdjunction (uliftRingMap (q n))
    let U := (ModuleCat.restrictScalars.{u + 1} (uliftRingMap (q n))).mapDerivedCategory
    let η : S (n + 1) ⟶ U.obj (S n) := adj.unit.app (S (n + 1)) ≫ U.map e.hom
    have hη (Z : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (A n)))) :
        Function.Bijective fun g : S n ⟶ Z ↦ η ≫ U.map g := by
      have h := (adj.homEquiv (S (n + 1)) Z).bijective.comp
        (e.symm.homFromEquiv (Z := Z)).bijective
      simpa only [η, U, Function.comp_def, Iso.homFromEquiv_apply, Iso.symm_inv,
        Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] using h
    exact small_universal_arrow (q n) (S (n + 1)) (S n) (M (n + 1)) (M n)
      (hM (n + 1)) (hM n) (Classical.choice (eM (n + 1))) (Classical.choice (eM n)) η hη
  choose f hf using hf
  exact ⟨M, hM, eM, f, hf⟩

end AlgebraicGeometry.ProEtale.IntegralSmallPerfect
