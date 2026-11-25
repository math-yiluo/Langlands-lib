/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexPresentation
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteModelProofAPI
import WeilConjectures.AlgebraicGeometry.CondensedSheafExtContinuity
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
/-! # Finite coefficient models are closed under extensions
Source: upstream `ModuleObject/Colimit/TwoColimit.lean`, Hom and object-descent
arguments. The Hom argument does not use object descent. We use it independently
of the two-colimit theorem to descend the boundary map of a short exact sequence.
-/
@[expose] public section
universe u wC wD wE vC vD vE uC uD uE
open CategoryTheory Limits MonoidalCategory MonObj Abelian ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor
-- Keep resolution comparisons from expanding during instance matching.
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

namespace AlgebraicGeometry.ProEtale
private instance moduleTensorFour {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (A B C D : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)),
      GradedObject.HasTensor₄ObjExt A B C D := by infer_instance
private instance moduleTensorLeft {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensor₁₂Tensor A B C := by infer_instance
private instance moduleTensorRight {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensorTensor₂₃ A B C := by infer_instance
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl
variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
  (ℓ : ℕ) [Fact ℓ.Prime]

private noncomputable instance finiteCommShift {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) : (derivedExtendScalarsSubfield X ℓ h).CommShift ℤ :=
  Functor.CommShift.ofIso
    (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)
      |>.leftDerivedFunctorIsoMapDerivedCategory).symm ℤ

private lemma singleHomDescent
    (E F : FiniteIntermediateField ℓ)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (hM : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E) M)
    (L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ F))) (hL : DerivedCategory.TStructure.t.plus L)
    (f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (derivedExtendScalarsToPadicAlgCl X ℓ F).obj L) :
    ∃ (H : FiniteIntermediateField ℓ) (he : E ≤ H) (hf : F ≤ H)
      (g : (derivedExtendScalarsSubfield X ℓ he).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
        (derivedExtendScalarsSubfield X ℓ hf).obj L),
      f = (derivedExtendScalarsCompIso X ℓ he).inv.app _ ≫
        (derivedExtendScalarsToPadicAlgCl X ℓ H).map g ≫
        (derivedExtendScalarsCompIso X ℓ hf).hom.app L := by
  let G := IsFiltered.max E F
  let I := AsSmall.{u + 1} (Under G)
  let H : I ⥤ FiniteIntermediateField ℓ :=
    (AsSmall.equiv (C := Under G)).inverse ⋙ Under.forget G
  let : H.Final := by dsimp [H]; infer_instance
  have he (i : I) : E ≤ H.obj i :=
    le_trans (leOfHom (IsFiltered.leftToMax E F)) (leOfHom (ULift.down i).hom)
  have hf (i : I) : F ≤ H.obj i :=
    le_trans (leOfHom (IsFiltered.rightToMax E F)) (leOfHom (ULift.down i).hom)
  obtain ⟨N, c, ⟨hc⟩, hN, eΩ, ei, hcomp⟩ :=
    exists_condensed_coefficient_complex_presentation X ℓ E F L hL H he hf
  let : HasColimit N := ⟨⟨c, hc⟩⟩
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  have hfac := CategoryTheory.factors_of_colimit_cocone N DerivedCategory.Q c hc K
    (CategoryTheory.factors_iso _ ((shiftFunctorZero _ ℤ).app K)
      (CategoryTheory.shiftFactors_of_hom_colimit N DerivedCategory.Q K
        (fun n ↦ isIso_constructible_condensed_sheaf_hom_colimit X ℓ E M hM N hN n) 0))
  let adj := finiteCoefficientDerivedAlgClHomEquiv X ℓ E K
    ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj L)
  obtain ⟨i, g, hg⟩ := hfac (adj f ≫ eΩ.inv)
  refine ⟨H.obj i, he i, hf i,
    (finiteCoefficientDerivedHomEquiv X ℓ (he i) K _).symm (g ≫ (ei i).hom), ?_⟩
  apply adj.injective
  have hh := hcomp i K g
  have hh' : adj f = (g ≫ DerivedCategory.Q.map (c.ι.app i)) ≫ eΩ.hom :=
    eΩ.comp_inv_eq.mp hg
  exact hh'.trans ((Category.assoc _ _ _).trans hh.symm)

private noncomputable def algClDerivedIso (E : FiniteIntermediateField ℓ) :
    derivedExtendScalarsToPadicAlgCl X ℓ E ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory :=
  (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))
    |>.leftDerivedFunctorIsoMapDerivedCategory
private noncomputable instance algClCommShift (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).CommShift ℤ :=
  Functor.CommShift.ofIso (algClDerivedIso X ℓ E).symm ℤ
private instance algClTriangulated (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated := by
  have := Functor.CommShift.ofIso_compatibility (algClDerivedIso X ℓ E).symm ℤ
  exact Functor.isTriangulated_of_iso (algClDerivedIso X ℓ E).symm
omit [TopologicalSpace.NoetherianSpace X] in
private lemma tensorCompShift {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    NatTrans.CommShift (derivedExtendScalarsCompIso X ℓ h).hom ℤ := by
  exact Functor.leftComp_shift
    (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F))
    ((Mod.extendScalarsComp _ _).symm ≪≫
      Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))

@[reassoc] private lemma boundary_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (e : F ⋙ G ≅ H) [NatTrans.CommShift e.hom ℤ]
    {A : C} {B : D} (g : B ⟶ F.obj (A⟦(1 : ℤ)⟧)) :
    G.map g ≫ G.map ((F.commShiftIso (1 : ℤ)).hom.app A) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (F.obj A) ≫ e.hom.app A⟦(1 : ℤ)⟧' =
      G.map g ≫ e.hom.app (A⟦(1 : ℤ)⟧) ≫ (H.commShiftIso (1 : ℤ)).hom.app A := by
  have hc := NatTrans.shift_app_comm e.hom (1 : ℤ) A
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hc
  exact congrArg (G.map g ≫ ·) hc

private lemma cancel_comparison
    {C : Type*} [Category C] {A B C' D : C}
    (e : A ≅ B) (g : A ⟶ C') (h : C' ⟶ D) (f : B ⟶ D)
    (hf : f = e.inv ≫ g ≫ h) : g ≫ h = e.hom ≫ f := by
  rw [hf, ← Category.assoc, ← Category.assoc, e.hom_inv_id, Category.id_comp]

private lemma boundary_identification
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (e : F ⋙ G ≅ H) [NatTrans.CommShift e.hom ℤ]
    (A : C) (B : D) {K₁ K₃ : E}
    (e₁ : H.obj A ≅ K₁) (e₃ : G.obj B ≅ K₃)
    (δ : K₃ ⟶ K₁⟦(1 : ℤ)⟧) (g : B ⟶ F.obj (A⟦(1 : ℤ)⟧))
    (hg : G.map g ≫ e.hom.app (A⟦(1 : ℤ)⟧) =
      e₃.hom ≫ δ ≫ e₁.inv⟦(1 : ℤ)⟧' ≫ (H.commShiftIso (1 : ℤ)).inv.app A) :
    (G.map (g ≫ (F.commShiftIso (1 : ℤ)).hom.app A) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (F.obj A)) ≫
      (e.app A ≪≫ e₁).hom⟦(1 : ℤ)⟧' = e₃.hom ≫ δ := by
  dsimp only [Iso.trans_hom]
  simp only [Functor.map_comp, Iso.app_hom, Category.assoc]
  rw [boundary_transport_assoc F G H e g, ← Category.assoc, hg]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, e₁.inv_hom_id]
  simp

attribute [local irreducible] derivedExtendScalarsCompIso

/-- Finite constructible coefficient models are closed under distinguished extensions.
Source: upstream `ModuleObject/Colimit/TwoColimit.lean`, Hom and object descent.
(auxiliary; not a blueprint node)
Proof: represent the boundary of the given triangle as a map from the single complex
of the third finite model into the scalar extension of the shifted first finite model.
The coefficient-complex presentation and constructible Hom continuity descend this
map to one common finite stage. Complete it to a distinguished triangle there. Serre
closure and exact coefficient extension make its middle object bounded constructible.
The tensor comparisons commute with shifts, so its extended boundary is the given
boundary. The triangle isomorphism axiom identifies the two middle objects. Taking
zeroth cohomology and commuting it with exact scalar extension gives the desired model.
The endpoint models may be zero and may be over different fields.
-/
theorem exists_finiteCoefficient_model_of_triangle
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (D : Pretriangulated.Triangle (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))))
    (hD : D ∈ distTriang _)
    (h₁ : ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E) P ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj P) ≅ D.obj₁))
    (h₃ : ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E) P ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj P) ≅ D.obj₃)) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E) P ∧
      Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj P ≅
        (DerivedCategory.homologyFunctor _ 0).obj D.obj₂) := by
  obtain ⟨E, P, hP, ⟨eP⟩⟩ := h₁
  obtain ⟨F, Q, hQ, ⟨eQ⟩⟩ := h₃
  let KP := (DerivedCategory.singleFunctor _ 0).obj P
  let KQ := (DerivedCategory.singleFunctor _ 0).obj Q
  let extE := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  let extF := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)
  let e₁ := (algClDerivedIso X ℓ E).app KP ≪≫
    (extE.mapDerivedCategorySingleFunctor 0).app P ≪≫ eP
  let e₃ := (algClDerivedIso X ℓ F).app KQ ≪≫
    (extF.mapDerivedCategorySingleFunctor 0).app Q ≪≫ eQ
  let L := KP⟦(1 : ℤ)⟧
  have hL : DerivedCategory.TStructure.t.plus L := by
    exact ⟨-1, DerivedCategory.TStructure.t.isGE_shift KP 0 1 (-1) (by decide)⟩
  let f := e₃.hom ≫ D.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧' ≫
    ((derivedExtendScalarsToPadicAlgCl X ℓ E).commShiftIso (1 : ℤ)).inv.app KP
  obtain ⟨H, hf, he, g, hg⟩ := singleHomDescent X ℓ F E Q hQ L hL f
  let A := (derivedExtendScalarsSubfield X ℓ he).obj KP
  let C := (derivedExtendScalarsSubfield X ℓ hf).obj KQ
  let g' : C ⟶ A⟦(1 : ℤ)⟧ :=
    g ≫ ((derivedExtendScalarsSubfield X ℓ he).commShiftIso (1 : ℤ)).hom.app KP
  obtain ⟨B, a, b, hB⟩ := Pretriangulated.distinguished_cocone_triangle₂ g'
  have hA : boundedConstructible (padicSubfieldRingObj X ℓ H) A :=
    boundedConstructible_leftDerivedExtendScalars_obj _ _ _ KP
      (CondensedRing.boundedConstructible_singleFunctor_zero_obj _ P hP)
  have hC : boundedConstructible (padicSubfieldRingObj X ℓ H) C :=
    boundedConstructible_leftDerivedExtendScalars_obj _ _ _ KQ
      (CondensedRing.boundedConstructible_singleFunctor_zero_obj _ Q hQ)
  have := isTriangulated_boundedConstructible_continuousMapRingObj X ℓ H
  have : (boundedConstructible (padicSubfieldRingObj X ℓ H)).IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1,
      fun n ↦ constructible_of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso e) (h.2 n)⟩⟩
  have hmiddle : boundedConstructible (padicSubfieldRingObj X ℓ H) B :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₂ _ hB hA hC
  let W := derivedExtendScalarsToPadicAlgCl X ℓ H
  let eA := (derivedExtendScalarsCompIso X ℓ he).app KP ≪≫ e₁
  let eC := (derivedExtendScalarsCompIso X ℓ hf).app KQ ≪≫ e₃
  have hcomm : (W.mapTriangle.obj (Pretriangulated.Triangle.mk a b g')).mor₃ ≫
      eA.hom⟦(1 : ℤ)⟧' = eC.hom ≫ D.mor₃ := by
    have := tensorCompShift X ℓ he
    have hh : W.map g ≫ (derivedExtendScalarsCompIso X ℓ he).hom.app L =
        (derivedExtendScalarsCompIso X ℓ hf).hom.app KQ ≫ f :=
      cancel_comparison ((derivedExtendScalarsCompIso X ℓ hf).app KQ)
        (W.map g) ((derivedExtendScalarsCompIso X ℓ he).hom.app L) f hg
    have hh' : W.map g ≫
        (derivedExtendScalarsCompIso X ℓ he).hom.app (KP⟦(1 : ℤ)⟧) =
        eC.hom ≫ D.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧' ≫
          ((derivedExtendScalarsToPadicAlgCl X ℓ E).commShiftIso (1 : ℤ)).inv.app KP := by
      simpa only [eC, Iso.trans_hom, Iso.app_hom, f, Category.assoc] using hh
    exact boundary_identification (derivedExtendScalarsSubfield X ℓ he) W
      (derivedExtendScalarsToPadicAlgCl X ℓ E)
      (derivedExtendScalarsCompIso X ℓ he) KP C e₁ eC D.mor₃ g hh'
  let e := Pretriangulated.Triangle.π₂.mapIso
    (Pretriangulated.isoTriangleOfIso₁₃ _ _ (W.map_distinguished _ hB) hD eA eC hcomm)
  refine ⟨H, (DerivedCategory.homologyFunctor _ 0).obj B, hmiddle.2 0, ⟨?_⟩⟩
  let ext := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ H)
  exact (ext.mapDerivedCategoryHomologyFunctorIso 0).app B ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso
      ((algClDerivedIso X ℓ H).app B).symm ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso e

end AlgebraicGeometry.ProEtale
