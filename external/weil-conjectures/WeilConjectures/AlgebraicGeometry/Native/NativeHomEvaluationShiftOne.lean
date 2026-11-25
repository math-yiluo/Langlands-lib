/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeDerivedClosedTensorShifts

/-! # Evaluation and the signed source shift in degree one

## References

* Stacks Project, Tags 08J9 and 08JC, the evaluation transpose of the signed reindexing of the
  product Hom complex
* Stacks Project, Tag 08JC, signed Hom-complex evaluation calculation
* Stacks Project, Tag 08JC, Hom-complex signs and evaluation
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

private lemma sourceShift_inv_uncurry
    {D : Type d} [Category.{u} D] [Preadditive D] [HasShift D ℤ]
    [MonoidalCategory D] [MonoidalClosed D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]
    (K M T : D) (n : ℤ) (f : T ⟶ ((ihom K).obj M)⟦-n⟧) :
    MonoidalClosed.uncurry (f ≫ (siteHomSourceShift K n).inv.app M) =
      (((curriedTensor D).flip.obj T).commShiftIso n).hom.app K ≫
        ((tensorLeft K).commShiftIso n).inv.app T ≫
        K ◁ f⟦n⟧' ≫
        K ◁ (shiftFunctorCompIsoId D (-n) n (by omega)).hom.app ((ihom K).obj M) ≫
        (ihom.adjunction K).counit.app M := by
  let α := (tensorLeft K).commShiftIso n ≪≫
    (siteHomTensorParameterShift K n).symm
  let adj := ((shiftEquiv D n).toAdjunction.comp (ihom.adjunction K)).ofNatIsoLeft α
  delta siteHomSourceShift
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eq,
    Adjunction.rightAdjointUniq_inv_app]
  change (tensorLeft (K⟦n⟧)).map f ≫
    (tensorLeft (K⟦n⟧)).map
      ((adj.rightAdjointUniq (ihom.adjunction (K⟦n⟧))).hom.app M) ≫
        (ihom.adjunction (K⟦n⟧)).counit.app M = _
  erw [Adjunction.rightAdjointUniq_hom_app_counit]
  have hc : adj.counit.app M =
      α.inv.app (((ihom K).obj M)⟦-n⟧) ≫
        (tensorLeft K).map ((shiftFunctorCompIsoId D (-n) n (by omega)).hom.app
          ((ihom K).obj M)) ≫ (ihom.adjunction K).counit.app M := by
    dsimp only [adj]
    erw [Adjunction.ofNatIsoLeft_counit]
    simp only [NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app]
    erw [Adjunction.comp_counit_app]
    rfl
  erw [hc, ← Category.assoc, α.inv.naturality]
  dsimp only [α]
  delta siteHomTensorParameterShift
  change (((((curriedTensor D).flip.obj T).commShiftIso n).hom.app K ≫
      ((tensorLeft K).commShiftIso n).inv.app T) ≫ K ◁ f⟦n⟧') ≫
      K ◁ (shiftFunctorCompIsoId D (-n) n (by omega)).hom.app ((ihom K).obj M) ≫
        (ihom.adjunction K).counit.app M = _
  simp only [Category.assoc]

private lemma sourceShift_inv_shift_uncurry
    {D : Type d} [Category.{u} D] [Preadditive D] [HasShift D ℤ]
    [MonoidalCategory D] [MonoidalClosed D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]
    (K M T U : D) (f : T ⟶ U⟦(1 : ℤ)⟧) (e : U ⟶ (ihom K).obj M) :
    MonoidalClosed.uncurry ((f ≫ e⟦(1 : ℤ)⟧') ≫
        (siteHomOppositeSourceShift K 1).inv.app M) =
      (((curriedTensor D).flip.obj T).commShiftIso (-1)).hom.app K ≫
        ((K ◁ f) ≫ ((tensorLeft K).commShiftIso (1 : ℤ)).hom.app U ≫
          (MonoidalClosed.uncurry e)⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId D 1 (-1) (by omega)).hom.app M := by
  delta siteHomOppositeSourceShift
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    CategoryTheory.Functor.whiskerLeft_app, eqToIso.inv, eqToHom_refl,
    NatTrans.id_app]
  erw [Category.id_comp]
  erw [sourceShift_inv_uncurry]
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  erw [← (tensorLeft K).commShiftIso_inv_naturality_assoc f (-1 : ℤ)]
  erw [← MonoidalCategory.whiskerLeft_comp_assoc,
    (shiftFunctorCompIsoId D 1 (-1) (by omega)).hom.naturality e,
    MonoidalCategory.whiskerLeft_comp_assoc]
  have h := (tensorLeft K).map_shiftFunctorCompIsoId_hom_app U (1 : ℤ) (-1) (by omega)
  change K ◁ _ = _ at h
  erw [h]
  simp only [Category.assoc, CategoryTheory.Functor.id_map]
  erw [Iso.inv_hom_id_app_assoc]
  erw [← (shiftFunctorCompIsoId D 1 (-1) (by omega)).hom.naturality
    (MonoidalClosed.uncurry e)]
  simp only [MonoidalClosed.uncurry_eq, CategoryTheory.Functor.comp_map,
    curriedTensor_obj_map]

private lemma uncurry_nativeHom_comparison
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P I : CochainComplex C ℤ) :
    MonoidalClosed.uncurry (DerivedCategory.qhInternalHomToIhom P I) =
      Functor.LaxMonoidal.μ DerivedCategory.Q P (CochainComplex.internalHomObj P I) ≫
        DerivedCategory.Q.map ((CochainComplex.tensorHomAdjunction P).counit.app I) := by
  rw [DerivedCategory.qhInternalHomToIhom, MonoidalClosed.uncurry_curry]
  have hμ : Functor.LaxMonoidal.μ DerivedCategory.Q P
      (CochainComplex.internalHomObj P I) =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj
          (CochainComplex.internalHomObj P I)) := by
    change (𝟙 _ ⊗ₘ 𝟙 _) ≫ (_ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫ 𝟙 _ = _
    simp
  rw [hμ]
  congr 1

private lemma nativeHom_comparison_transport
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P I : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).inv.app (CochainComplex.internalHomObj P I) ≫
        DerivedCategory.qhInternalHomToIhom P I ≫
        (ihom (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj P))).map
          ((DerivedCategory.quotientCompQhIso C).hom.app I) ≫
        (MonoidalClosed.pre ((DerivedCategory.quotientCompQhIso C).inv.app P)).app
          (DerivedCategory.Q.obj I) = DerivedCategory.qhInternalHomToIhom P I := by
  change (𝟙 _ ≫ DerivedCategory.qhInternalHomToIhom P I ≫
    (ihom (DerivedCategory.Q.obj P)).map (𝟙 (DerivedCategory.Q.obj I)) ≫
    (MonoidalClosed.pre (𝟙 (DerivedCategory.Q.obj P))).app (DerivedCategory.Q.obj I)) = _
  simp only [MonoidalClosed.pre_id, NatTrans.id_app, Category.id_comp, Category.comp_id]
  erw [(ihom (DerivedCategory.Q.obj P)).map_id, Category.comp_id]

private lemma localize_evaluation_shift
    {E : Type*} {D : Type*} [Category E] [Category D]
    [HasShift E ℤ] [HasShift D ℤ] [MonoidalCategory E] [MonoidalCategory D]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [(curriedTensor D).CommShift₂Int]
    (Q : E ⥤ D) [Q.LaxMonoidal] [Q.CommShift ℤ]
    (X U J : E)
    (s₁ : X⟦(-1 : ℤ)⟧ ⊗ U⟦(1 : ℤ)⟧ ⟶ (X ⊗ U⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧)
    (s₂ : X ⊗ U⟦(1 : ℤ)⟧ ⟶ (X ⊗ U)⟦(1 : ℤ)⟧)
    (ev : X ⊗ U ⟶ J)
    (h₁ : Functor.LaxMonoidal.μ Q (X⟦(-1 : ℤ)⟧) (U⟦(1 : ℤ)⟧) ≫ Q.map s₁ ≫
        (Q.commShiftIso (-1 : ℤ)).hom.app (X ⊗ U⟦(1 : ℤ)⟧) =
      ((Q.commShiftIso (-1 : ℤ)).hom.app X) ▷ Q.obj (U⟦(1 : ℤ)⟧) ≫
        (((curriedTensor D).flip.obj (Q.obj (U⟦(1 : ℤ)⟧))).commShiftIso (-1)).hom.app
          (Q.obj X) ≫ (Functor.LaxMonoidal.μ Q X (U⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧')
    (h₂ : Functor.LaxMonoidal.μ Q X (U⟦(1 : ℤ)⟧) ≫ Q.map s₂ ≫
        (Q.commShiftIso (1 : ℤ)).hom.app (X ⊗ U) =
      Q.obj X ◁ (Q.commShiftIso (1 : ℤ)).hom.app U ≫
        ((tensorLeft (Q.obj X)).commShiftIso (1 : ℤ)).hom.app (Q.obj U) ≫
          (Functor.LaxMonoidal.μ Q X U)⟦(1 : ℤ)⟧') :
    ((Q.commShiftIso (-1 : ℤ)).inv.app X) ▷ Q.obj (U⟦(1 : ℤ)⟧) ≫
        Functor.LaxMonoidal.μ Q (X⟦(-1 : ℤ)⟧) (U⟦(1 : ℤ)⟧) ≫
        Q.map (s₁ ≫ s₂⟦(-1 : ℤ)⟧' ≫
          (shiftFunctorCompIsoId E 1 (-1) (by omega)).hom.app (X ⊗ U) ≫ ev) =
      (((curriedTensor D).flip.obj (Q.obj (U⟦(1 : ℤ)⟧))).commShiftIso (-1)).hom.app
          (Q.obj X) ≫
        ((Q.obj X ◁ (Q.commShiftIso (1 : ℤ)).hom.app U) ≫
          ((tensorLeft (Q.obj X)).commShiftIso (1 : ℤ)).hom.app (Q.obj U) ≫
          (Functor.LaxMonoidal.μ Q X U ≫ Q.map ev)⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId D 1 (-1) (by omega)).hom.app (Q.obj J) := by
  let T := U⟦(1 : ℤ)⟧
  let B := X ⊗ U
  let lam := (((curriedTensor D).flip.obj (Q.obj T)).commShiftIso (-1 : ℤ)).hom.app
    (Q.obj X)
  let rho := ((tensorLeft (Q.obj X)).commShiftIso (1 : ℤ)).hom.app (Q.obj U)
  have h₁' : ((Q.commShiftIso (-1 : ℤ)).inv.app X) ▷ Q.obj T ≫
      Functor.LaxMonoidal.μ Q (X⟦(-1 : ℤ)⟧) T ≫ Q.map s₁ =
        lam ≫ (Functor.LaxMonoidal.μ Q X T)⟦(-1 : ℤ)⟧' ≫
          (Q.commShiftIso (-1 : ℤ)).inv.app (X ⊗ T) := by
    simp only [← Category.assoc]
    erw [Iso.eq_comp_inv ((Q.commShiftIso (-1 : ℤ)).app (X ⊗ T))]
    simpa only [T, lam, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
      ← comp_whiskerRight_assoc, id_whiskerRight, Category.id_comp] using congrArg
        (fun f ↦ ((Q.commShiftIso (-1 : ℤ)).inv.app X) ▷ Q.obj T ≫ f) h₁
  have h₂' : Functor.LaxMonoidal.μ Q X T ≫ Q.map s₂ =
      Q.obj X ◁ (Q.commShiftIso (1 : ℤ)).hom.app U ≫ rho ≫
        (Functor.LaxMonoidal.μ Q X U)⟦(1 : ℤ)⟧' ≫
          (Q.commShiftIso (1 : ℤ)).inv.app B := by
    simp only [← Category.assoc]
    erw [Iso.eq_comp_inv ((Q.commShiftIso (1 : ℤ)).app B)]
    simpa only [T, B, rho, Iso.app_hom, Category.assoc] using h₂
  change _ = lam ≫ _
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% h₁', ← Q.commShiftIso_inv_naturality_assoc s₂ (-1 : ℤ)]
  rw [← (shiftFunctor D (-1 : ℤ)).map_comp_assoc, h₂']
  simp only [Functor.map_comp, Category.assoc]
  rw [Q.map_shiftFunctorCompIsoId_hom_app B 1 (-1) (by omega)]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [← (shiftFunctor D (-1 : ℤ)).map_comp_assoc, Iso.inv_hom_id_app]
  have hn : (shiftFunctorCompIsoId D 1 (-1) (by omega)).hom.app (Q.obj B) ≫
      Q.map ev = (Q.map ev)⟦(1 : ℤ)⟧'⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId D 1 (-1) (by omega)).hom.app (Q.obj J) := by
    simpa only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] using
      ((shiftFunctorCompIsoId D 1 (-1) (by omega)).hom.naturality (Q.map ev)).symm
  rw [hn]
  simp only [Functor.map_comp, Category.assoc]
  erw [(shiftFunctor D (-1 : ℤ)).map_id, Category.id_comp]

-- Matching Q with quotient followed by Qh unfolds the localization instance data.
private lemma evaluation_shift_localization
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P I : CochainComplex C ℤ) :
    ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app P) ▷
          DerivedCategory.Q.obj ((CochainComplex.internalHomObj P I)⟦(1 : ℤ)⟧) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (P⟦(-1 : ℤ)⟧)
          ((CochainComplex.internalHomObj P I)⟦(1 : ℤ)⟧) ≫
        DerivedCategory.Q.map
          ((CochainComplex.mapBifunctorShift₁Iso P
              ((CochainComplex.internalHomObj P I)⟦(1 : ℤ)⟧)
              (curriedTensor C) (-1)).hom ≫
            ((CochainComplex.mapBifunctorShift₂Iso P
              (CochainComplex.internalHomObj P I) (curriedTensor C) 1).hom)⟦(-1 : ℤ)⟧' ≫
            (shiftFunctorCompIsoId (CochainComplex C ℤ) 1 (-1) (by omega)).hom.app _ ≫
            (CochainComplex.tensorHomAdjunction P).counit.app I) =
      (((curriedTensor (DerivedCategory C)).flip.obj
          (DerivedCategory.Q.obj ((CochainComplex.internalHomObj P I)⟦(1 : ℤ)⟧))).commShiftIso
            (-1 : ℤ)).hom.app (DerivedCategory.Q.obj P) ≫
        ((DerivedCategory.Q.obj P ◁
              (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
                (CochainComplex.internalHomObj P I)) ≫
            ((tensorLeft (DerivedCategory.Q.obj P)).commShiftIso (1 : ℤ)).hom.app
              (DerivedCategory.Q.obj (CochainComplex.internalHomObj P I)) ≫
            (MonoidalClosed.uncurry
              (DerivedCategory.qhInternalHomToIhom P I))⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (DerivedCategory C) 1 (-1) (by omega)).hom.app
          (DerivedCategory.Q.obj I) := by
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let U := CochainComplex.internalHomObj P I
  let B := P ⊗ U
  let T := U⟦(1 : ℤ)⟧
  let s₁ := (CochainComplex.mapBifunctorShift₁Iso P T (curriedTensor C) (-1)).hom
  let s₂ := (CochainComplex.mapBifunctorShift₂Iso P U (curriedTensor C) 1).hom
  let lam := (((curriedTensor (DerivedCategory C)).flip.obj (Q.obj T)).commShiftIso
    (-1 : ℤ)).hom.app (Q.obj P)
  let rho := ((tensorLeft (Q.obj P)).commShiftIso (1 : ℤ)).hom.app (Q.obj U)
  let ev := (CochainComplex.tensorHomAdjunction P).counit.app I
  obtain ⟨_, h₁, h₂, _⟩ := DerivedCategory.nativeDerivedClosedTensorShifts C
  have h₁ := h₁ P T (-1)
  have h₂ := h₂ P U 1
  simp only [Functor.uncurry_obj_map, Prod.mkHom,
    curriedTensor_map_app, curriedTensor_obj_map, whiskerLeft_id, id_whiskerRight] at h₁ h₂
  change Functor.LaxMonoidal.μ Q (P⟦(-1 : ℤ)⟧) T ≫ Q.map s₁ ≫
      (Q.commShiftIso (-1 : ℤ)).hom.app (P ⊗ T) =
    (((Q.commShiftIso (-1 : ℤ)).hom.app P) ▷ Q.obj T ≫ 𝟙 _) ≫
      lam ≫ (Functor.LaxMonoidal.μ Q P T)⟦(-1 : ℤ)⟧' at h₁
  change Functor.LaxMonoidal.μ Q P T ≫ Q.map s₂ ≫
      (Q.commShiftIso (1 : ℤ)).hom.app B =
    (𝟙 _ ≫ Q.obj P ◁ (Q.commShiftIso (1 : ℤ)).hom.app U) ≫
      rho ≫ (Functor.LaxMonoidal.μ Q P U)⟦(1 : ℤ)⟧' at h₂
  simp only [Category.comp_id] at h₁
  simp only [Category.id_comp] at h₂
  erw [uncurry_nativeHom_comparison]
  exact localize_evaluation_shift Q P U I s₁ s₂ ev h₁ h₂

/-- The signed source reindexing commutes with ordinary tensor evaluation. -/
private lemma nativeHom_evaluation_shift_one_model
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (P I : CochainComplex C ℤ)
    (σ : (CochainComplex.internalHomObj P I)⟦(1 : ℤ)⟧ ⟶
      CochainComplex.internalHomObj (P⟦(-1 : ℤ)⟧) I)
    (hσ : ∀ (n p q : ℤ) (hpq : p + n = q),
      σ.f n ≫ CochainComplex.internalHomπ (P⟦(-1 : ℤ)⟧) I n p q hpq =
        p.negOnePow • CochainComplex.internalHomπ P I (n + 1) (p + -1) q (by omega)) :
    (P⟦(-1 : ℤ)⟧) ◁ σ ≫
        (CochainComplex.tensorHomAdjunction (P⟦(-1 : ℤ)⟧)).counit.app I =
      -((CochainComplex.mapBifunctorShift₁Iso P
            ((CochainComplex.internalHomObj P I)⟦(1 : ℤ)⟧) (curriedTensor C) (-1)).hom ≫
          ((CochainComplex.mapBifunctorShift₂Iso P
            (CochainComplex.internalHomObj P I) (curriedTensor C) 1).hom)⟦(-1 : ℤ)⟧' ≫
          (shiftFunctorCompIsoId (CochainComplex C ℤ) 1 (-1) (by omega)).hom.app _ ≫
          (CochainComplex.tensorHomAdjunction P).counit.app I) := by
  let ev : P ⊗ CochainComplex.internalHomObj P I ⟶ I :=
    (CochainComplex.internalHomEquiv P I _).symm (𝟙 _)
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply,
    Preadditive.comp_neg]
  rw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc]
  rw [CochainComplex.tensorHomAdjunction_counit_app,
    CochainComplex.ιTensorObj_internalHomEquiv_symm_f]
  simp only [HomologicalComplex.id_f, Category.id_comp]
  rw [← MonoidalClosed.uncurry_natural_left, hσ]
  rw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc P
    ((CochainComplex.internalHomObj P I)⟦(1 : ℤ)⟧) (curriedTensor C) (-1)
    p q n hpq (p + -1) (n + -1) rfl rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  simp only [curriedTensor_map_app,
    CochainComplex.shiftFunctor_map_f']
  erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc P
    (CochainComplex.internalHomObj P I) (curriedTensor C) 1
    (p + -1) q (n + -1) (by change p + q = n at hpq; omega)
    (q + 1) ((n + -1) + 1) rfl rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, curriedTensor_obj_map,
    Category.comp_id, mul_one,
    Linear.units_smul_comp, MonoidalClosed.uncurry_units_smul]
  erw [id_whiskerRight, Category.id_comp, whiskerLeft_id, Category.id_comp]
  simp only [shiftFunctorCompIsoId, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    HomologicalComplex.comp_f, CochainComplex.shiftFunctorAdd'_inv_app_f',
    CochainComplex.shiftFunctorZero_hom_app_f]
  change p.negOnePow •
      MonoidalClosed.uncurry (CochainComplex.internalHomπ P I (q + 1) (p + -1) n
        (by change p + q = n at hpq; omega)) =
    -((p + -1).negOnePow •
      (P.ιMapBifunctor (CochainComplex.internalHomObj P I) (curriedTensor C)
        (p + -1) (q + 1) (n + -1 + 1) (by change p + q = n at hpq; omega)) ≫
      ((HomologicalComplex.XIsoOfEq (P ⊗ CochainComplex.internalHomObj P I)
          (show n + -1 + 1 = n + 0 by omega)).hom ≫
        (HomologicalComplex.XIsoOfEq (P ⊗ CochainComplex.internalHomObj P I)
          (show n + 0 = n by omega)).hom) ≫
      ev.f n)
  have hi (r s : ℤ) (hr : p + -1 + (q + 1) = r)
      (hs : p + -1 + (q + 1) = s) (h : r = s) :
      P.ιMapBifunctor (CochainComplex.internalHomObj P I) (curriedTensor C)
          (p + -1) (q + 1) r hr ≫
        (HomologicalComplex.XIsoOfEq (P ⊗ CochainComplex.internalHomObj P I) h).hom =
      P.ιMapBifunctor (CochainComplex.internalHomObj P I) (curriedTensor C)
        (p + -1) (q + 1) s hs := by
    cases h
    erw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  erw [HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom]
  erw [reassoc_of% hi (n + -1 + 1) n
    (by change p + q = n at hpq; omega)
    (by change p + q = n at hpq; omega) (by omega)]
  dsimp only [ev]
  erw [CochainComplex.ιTensorObj_internalHomEquiv_symm_f]
  simp only [HomologicalComplex.id_f, Category.id_comp]
  rw [Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_one,
    mul_neg, mul_one, Units.neg_smul, neg_neg]

-- Comparing the fixed evaluation maps unfolds their localization and internal Hom data.
/-- The evaluation comparison respects the specified signed source shift in degree one. -/
theorem nativeHom_evaluation_shift_one
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (P I : CochainComplex C ℤ) [I.IsKInjective]
    (σ : (CochainComplex.internalHomObj P I)⟦(1 : ℤ)⟧ ⟶
      CochainComplex.internalHomObj (P⟦(-1 : ℤ)⟧) I)
    (hσ : ∀ (n p q : ℤ) (hpq : p + n = q),
      σ.f n ≫ CochainComplex.internalHomπ (P⟦(-1 : ℤ)⟧) I n p q hpq =
        p.negOnePow • CochainComplex.internalHomπ P I (n + 1) (p + -1) q (by omega)) :
    DerivedCategory.Q.map σ ≫
        (DerivedCategory.quotientCompQhIso C).inv.app
          (CochainComplex.internalHomObj (P⟦(-1 : ℤ)⟧) I) ≫
        DerivedCategory.qhInternalHomToIhom (P⟦(-1 : ℤ)⟧) I ≫
        (ihom (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient C (.up ℤ)).obj (P⟦(-1 : ℤ)⟧)))).map
            ((DerivedCategory.quotientCompQhIso C).hom.app I) ≫
        (MonoidalClosed.pre ((DerivedCategory.quotientCompQhIso C).inv.app
          (P⟦(-1 : ℤ)⟧))).app (DerivedCategory.Q.obj I) ≫
        (MonoidalClosed.internalHom.flip.obj (DerivedCategory.Q.obj I)).map
          ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app P).op ≫
        (MonoidalClosed.internalHom.flip.obj (DerivedCategory.Q.obj I)).map
          ((shiftFunctorOpIso (DerivedCategory C) 1 (-1) (by omega)).inv.app
            (op (DerivedCategory.Q.obj P))) ≫
        siteHomSignedSourceComponent (DerivedCategory.Q.obj I) 1
          (op (DerivedCategory.Q.obj P)) =
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (CochainComplex.internalHomObj P I) ≫
        ((DerivedCategory.quotientCompQhIso C).inv.app (CochainComplex.internalHomObj P I) ≫
          DerivedCategory.qhInternalHomToIhom P I ≫
          (ihom (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj P))).map
            ((DerivedCategory.quotientCompQhIso C).hom.app I) ≫
          (MonoidalClosed.pre ((DerivedCategory.quotientCompQhIso C).inv.app P)).app
            (DerivedCategory.Q.obj I))⟦(1 : ℤ)⟧' := by
  rw [reassoc_of% nativeHom_comparison_transport (P⟦(-1 : ℤ)⟧) I,
    nativeHom_comparison_transport P I]
  let K := DerivedCategory.Q.obj P
  let M := DerivedCategory.Q.obj I
  let U := CochainComplex.internalHomObj P I
  let T := DerivedCategory.Q.obj (U⟦(1 : ℤ)⟧)
  let e : DerivedCategory.Q.obj U ⟶ (ihom K).obj M :=
    DerivedCategory.qhInternalHomToIhom P I
  let es : DerivedCategory.Q.obj
      (CochainComplex.internalHomObj (P⟦(-1 : ℤ)⟧) I) ⟶
      (ihom (DerivedCategory.Q.obj (P⟦(-1 : ℤ)⟧))).obj M :=
    DerivedCategory.qhInternalHomToIhom (P⟦(-1 : ℤ)⟧) I
  change DerivedCategory.Q.map σ ≫ es ≫
    (MonoidalClosed.pre ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app P)).app M ≫
    (MonoidalClosed.internalHom.flip.obj M).map
      ((shiftFunctorOpIso (DerivedCategory C) 1 (-1) (by omega)).inv.app (op K)) ≫
    siteHomSignedSourceComponent M 1 (op K) =
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app U ≫ e⟦(1 : ℤ)⟧'
  have hs : siteHomSignedSourceComponent M 1 (op K) =
      -(siteHomOppositeSourceShift K 1).hom.app M := by
    simp only [siteHomSignedSourceComponent]
    norm_num
  rw [hs]
  have hk : (shiftFunctorOpIso (DerivedCategory C) 1 (-1) (by omega)).inv.app
      (op K) = 𝟙 _ := rfl
  erw [hk, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Preadditive.comp_neg]
  rw [neg_eq_iff_eq_neg]
  rw [← cancel_mono ((siteHomOppositeSourceShift K 1).inv.app M)]
  simp only [Category.assoc, Iso.hom_inv_id_app, Preadditive.neg_comp]
  erw [Category.comp_id]
  apply MonoidalClosed.uncurry_injective
  have hneg (g : T ⟶ (ihom (K⟦(-1 : ℤ)⟧)).obj M) :
      MonoidalClosed.uncurry (-g) = -MonoidalClosed.uncurry g :=
    map_neg (MonoidalClosed.curryAddEquiv (K⟦(-1 : ℤ)⟧) T M).symm g
  have hm := sourceShift_inv_shift_uncurry K M T (DerivedCategory.Q.obj U)
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app U) e
  simp only [Category.assoc] at hm
  rw [hneg, hm]
  let evs : (P⟦(-1 : ℤ)⟧) ⊗
      CochainComplex.internalHomObj (P⟦(-1 : ℤ)⟧) I ⟶ I :=
    (CochainComplex.tensorHomAdjunction (P⟦(-1 : ℤ)⟧)).counit.app I
  have hes : MonoidalClosed.uncurry es =
      Functor.LaxMonoidal.μ DerivedCategory.Q (P⟦(-1 : ℤ)⟧)
        (CochainComplex.internalHomObj (P⟦(-1 : ℤ)⟧) I) ≫
      DerivedCategory.Q.map evs :=
    uncurry_nativeHom_comparison (P⟦(-1 : ℤ)⟧) I
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app, hes]
  erw [whisker_exchange_assoc, Functor.LaxMonoidal.μ_natural_right_assoc]
  erw [← DerivedCategory.Q.map_comp, nativeHom_evaluation_shift_one_model P I σ hσ]
  simp only [CategoryTheory.Functor.map_neg, Preadditive.comp_neg]
  exact congrArg Neg.neg (evaluation_shift_localization P I)

end AlgebraicGeometry.ProEtale
