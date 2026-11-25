/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.InjectiveResolutionDerivedComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.Abelian.RightDerivedInjectiveBoundary
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift

/-!
# Boundary compatibility of the explicit resolution comparisons

Source: Stacks Project, Derived Categories, Tags 014Q, 05TE and 015B.
(blueprint: lem-sc-p1-horseshoe-comparison-boundary).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def resolutionPlus
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {X : A} (I : InjectiveResolution X) :
    CochainComplex.Plus A := ⟨I.cochainComplex, 0, inferInstance⟩

private theorem resolutionPlus_injective
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {X : A} (I : InjectiveResolution X) :
    ∀ n : ℤ, Injective ((resolutionPlus I).obj.X n) :=
  fun n ↦ inferInstanceAs (Injective (I.cochainComplex.X n))

private noncomputable def resolutionAugmentationIso
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [HasDerivedCategory.{w₁} A] {X : A} (I : InjectiveResolution X) :
    (DerivedCategory.Plus.singleFunctor A 0).obj X ≅
      DerivedCategory.Plus.Q.obj (resolutionPlus I) :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app X ≪≫
      asIso (DerivedCategory.Q.map I.ι'))

set_option maxHeartbeats 100000 in
-- The quotient factorization and the lifted unit involve several nested functors.
set_option backward.isDefEq.respectTransparency false in
private theorem comparison_eq_unit
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] {X : A} (I : InjectiveResolution X)
    [∀ n : ℤ, Injective ((resolutionPlus I).obj.X n)] :
    injectiveResolutionDerivedComparison v I =
      (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
          (resolutionAugmentationIso I).hom ≫
        boundedBelowInjectiveComparison v (resolutionPlus I) ≫
        DerivedCategory.Q.map (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat v).hom := by
  let R := injectiveResolution X
  have : ∀ n : ℤ, Injective ((resolutionPlus R).obj.X n) := resolutionPlus_injective R
  let φ : R.Hom I (𝟙 X) := ⟨InjectiveResolution.desc (𝟙 X) I R, by simp⟩
  let g : resolutionPlus R ⟶ resolutionPlus I := ObjectProperty.homMk φ.hom'
  let vg : v.rightDerivedPlusComplex X ⟶ v.mapCochainComplexPlus.obj (resolutionPlus I) :=
    ObjectProperty.homMk ((v.mapHomologicalComplex _).map φ.hom')
  have hη := v.rightDerivedFunctorPlusUnith.naturality
    ((HomotopyCategory.Plus.quotient A).map g)
  have ha : (resolutionAugmentationIso R).hom ≫ DerivedCategory.Plus.Q.map g =
      (resolutionAugmentationIso I).hom := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.map_comp, resolutionAugmentationIso, Functor.preimageIso_hom,
      Functor.map_preimage, Iso.trans_hom, Category.assoc]
    dsimp only [DerivedCategory.Plus.Q, Functor.comp_map, ObjectProperty.ι_map,
      HomotopyCategory.Plus.quotient, ObjectProperty.lift, g]
    simp only [ObjectProperty.homMk_hom, asIso_hom]
    rw [← DerivedCategory.Q.map_comp]
    simp [InjectiveResolution.Hom.ι'_comp_hom']
  have hu : inv (v.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient A).obj (resolutionPlus R))) ≫
      (DerivedCategory.Plus.Qh (C := B)).map ((HomotopyCategory.Plus.quotient B).map vg) =
    v.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.Qh (C := A)).map ((HomotopyCategory.Plus.quotient A).map g)) ≫
      inv (v.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient A).obj (resolutionPlus I))) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, eq_comm, IsIso.comp_inv_eq]
    exact hη.symm
  have he : (v.mapHomologicalComplex (.up ℤ)).map φ.hom' ≫
        (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat v).hom =
      (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat v).hom ≫
        HomologicalComplex.extendMap ((v.mapHomologicalComplex _).map φ.hom)
          ComplexShape.embeddingUpNat := by
    ext i
    exact HomologicalComplex.mapExtensIso_hom_f_naturality _ _ _ _
  have : IsIso (v.rightDerivedFunctorPlusUnit.app (resolutionPlus R)) :=
    isIso_rightDerivedFunctorPlusUnit_of_injective v (resolutionPlus R)
  have : IsIso (v.rightDerivedFunctorPlusUnit.app (resolutionPlus I)) :=
    isIso_rightDerivedFunctorPlusUnit_of_injective v (resolutionPlus I)
  simp only [injectiveResolutionDerivedComparison, boundedBelowInjectiveComparison,
    Functor.rightDerivedFunctorPlusObjSingleFunctorIsoQ, Iso.trans_hom,
    Iso.symm_hom, asIso_inv, Functor.map_comp, Category.assoc, Functor.comp_map]
  change DerivedCategory.Plus.ι.map
      (v.rightDerivedFunctorPlus.map (resolutionAugmentationIso R).hom) ≫
      DerivedCategory.Plus.ι.map (inv
        (v.rightDerivedFunctorPlusUnit.app (resolutionPlus R))) ≫
      DerivedCategory.Q.map (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat v).hom ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((v.mapHomologicalComplex _).map φ.hom) ComplexShape.embeddingUpNat) = _
  rw [← DerivedCategory.Q.map_comp, ← he, Functor.map_comp]
  change _ ≫ DerivedCategory.Plus.ι.map (inv
      (v.rightDerivedFunctorPlusUnit.app (resolutionPlus R))) ≫
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map vg) ≫ _ = _
  have hη' := v.rightDerivedFunctorPlusUnit.naturality g
  have hu' : inv (v.rightDerivedFunctorPlusUnit.app (resolutionPlus R)) ≫
        DerivedCategory.Plus.Q.map vg =
      v.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g) ≫
        inv (v.rightDerivedFunctorPlusUnit.app (resolutionPlus I)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, eq_comm, IsIso.comp_inv_eq]
    exact hη'.symm
  have hu'' := congrArg (fun f ↦ DerivedCategory.Plus.ι.map f) hu'
  simp only [Functor.map_comp] at hu''
  erw [reassoc_of% hu'']
  rw [← DerivedCategory.Plus.ι.map_comp_assoc, ← v.rightDerivedFunctorPlus.map_comp, ha]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem extension_shortExact
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (S : ShortComplex (CochainComplex A ℕ))
    (hS : S.ShortExact) :
    (S.map (ComplexShape.embeddingUpNat.extendFunctor A)).ShortExact := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
  intro k
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    let e : ((S.map (ComplexShape.embeddingUpNat.extendFunctor A)).map
        (HomologicalComplex.eval A (.up ℤ) (n : ℤ))) ≅
        S.map (HomologicalComplex.eval A (.up ℕ) n) :=
      ShortComplex.isoMk (S.X₁.extendXIso ComplexShape.embeddingUpNat rfl)
        (S.X₂.extendXIso ComplexShape.embeddingUpNat rfl)
        (S.X₃.extendXIso ComplexShape.embeddingUpNat rfl)
        (by dsimp; simp [HomologicalComplex.extendMap_f])
        (by dsimp; simp [HomologicalComplex.extendMap_f])
    exact ShortComplex.shortExact_of_iso e.symm
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n)
  · have hz (K : CochainComplex A ℕ) : IsZero ((K.extend ComplexShape.embeddingUpNat).X k) :=
      HomologicalComplex.isZero_extend_X K _ k (by intro n hn; dsimp at hn; omega)
    let T := (S.map (ComplexShape.embeddingUpNat.extendFunctor A)).map
      (HomologicalComplex.eval A (.up ℤ) k)
    have : IsIso T.g := by
      rw [(hz S.X₂).eq_of_src T.g 0]
      exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨hz S.X₂, hz S.X₃⟩
    exact (ShortComplex.Splitting.ofIsZeroOfIsIso T (hz S.X₁) inferInstance).shortExact

private noncomputable def resolutionShortComplex
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {X₁ X₂ X₃ : A} (IA : InjectiveResolution X₁) (IB : InjectiveResolution X₂)
    (IC : InjectiveResolution X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0) : ShortComplex (CochainComplex.Plus A) :=
  ShortComplex.mk
    (ObjectProperty.homMk (X := resolutionPlus IA) (Y := resolutionPlus IB)
      (HomologicalComplex.extendMap α ComplexShape.embeddingUpNat))
    (ObjectProperty.homMk (X := resolutionPlus IB) (Y := resolutionPlus IC)
      (HomologicalComplex.extendMap β ComplexShape.embeddingUpNat))
    (by ext; simp [← HomologicalComplex.extendMap_comp, hαβ])

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem augmentation_boundary
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [HasDerivedCategory.{w₁} A]
    (S : ShortComplex A) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι)
    (hH : ((resolutionShortComplex IA IB IC α β hαβ).map
      (CochainComplex.plus A).ι).ShortExact) :
    hS.singleTrianglePlus.mor₃ ≫ (resolutionAugmentationIso IA).hom⟦(1 : ℤ)⟧' =
      (resolutionAugmentationIso IC).hom ≫
        boundedBelowSESBoundary (resolutionShortComplex IA IB IC α β hαβ) hH := by
  let φ : IA.Hom IB S.f := ⟨α, by simpa using congrArg (fun f ↦ f.f 0) hιA⟩
  let ψ : IB.Hom IC S.g := ⟨β, by simpa using congrArg (fun f ↦ f.f 0) hιB⟩
  let a : S.map (HomologicalComplex.single A (.up ℤ) 0) ⟶
      (resolutionShortComplex IA IB IC α β hαβ).map (CochainComplex.plus A).ι :=
    { τ₁ := IA.ι'
      τ₂ := IB.ι'
      τ₃ := IC.ι'
      comm₁₂ := φ.ι'_comp_hom'
      comm₂₃ := ψ.ι'_comp_hom' }
  have hn := DerivedCategory.triangleOfSESδ_naturality
    (hS.map_of_exact (HomologicalComplex.single A (.up ℤ) 0)) hH a
  apply DerivedCategory.Plus.ι.map_injective
  apply (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
    (DerivedCategory.Plus.Q.obj (resolutionPlus IA)))).1
  simp only [Functor.map_comp, Category.assoc]
  erw [Functor.commShiftIso_hom_naturality]
  simp only [ShortComplex.ShortExact.singleTrianglePlus, Pretriangulated.Triangle.mk_mor₃,
    boundedBelowSESBoundary, Functor.map_preimage, Category.assoc]
  simp only [resolutionAugmentationIso, Functor.preimageIso_hom, Functor.map_preimage,
    Iso.trans_hom, Iso.app_hom, asIso_hom,
    Category.assoc]
  change (hS.singleδ ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁)) ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁) ≫
      (shiftFunctor (DerivedCategory A) 1).map
        (((DerivedCategory.singleFunctorIsoCompQ A 0).app S.X₁).hom ≫
          DerivedCategory.Q.map IA.ι') =
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app S.X₃).hom ≫
      DerivedCategory.Q.map IC.ι' ≫ DerivedCategory.triangleOfSESδ hH ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        (DerivedCategory.Plus.Q.obj (resolutionPlus IA)) ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Plus.Q.obj (resolutionPlus IA))
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Functor.map_comp]
  simp only [ShortComplex.ShortExact.singleδ]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.app_hom, Iso.refl_hom, NatTrans.id_app]
  erw [Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  exact hn

/-- The explicit comparisons respect the connecting arrow of the derived
horseshoe triangle.

Source: Stacks Project, Derived Categories, Tags 014Q, 0159 and 015B;
fixed-horseshoe comparison, Steps 1-3.
(blueprint: lem-sc-p1-horseshoe-comparison-boundary).

Proof:
1. Extend the compatible horseshoe and its augmentations by zero. Each degree
row splits because its first term is injective. Use the split triangle with
connecting chain map section, differential, retraction; its cone comparison fixes
the sign. The augmentation maps are quasi-isomorphisms.
2. Transport this triangle to the single objects. Maps from X₁[0][1] to X₃[0]
vanish: compute into the bounded below injective resolution of X₃ in the homotopy
category, where the supports are disjoint. Third-map uniqueness identifies the
transported boundary with the canonical single-triangle boundary.
3. Apply the derived functor. The unit is invertible on the three bounded below
injective complexes. Its naturality supplies the first two squares; its shift
compatibility supplies the third square. Termwise additivity preserves the split
connecting map and the minus sign in the shifted differential. Commute the
termwise functor past extension by zero using mapExtendIso.
4. The comparisons in Steps 2-3 equal the explicit comparisons below: compose
with a lift of the identity from the chosen resolution. Any two such lifts are
homotopic, so their localized maps agree. Naturality of the derived unit applied
to this lift identifies the inverse-unit comparison for the fixed resolution
with the chosen-resolution comparison followed by the lift. The quotient
factorization and mapExtendIso identify its target with Q(EvI). Thus the first
and third components are exactly the displayed explicit comparisons, and the
third triangle square is the asserted equation.
-/
theorem horseshoe_comparison_boundary
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (S : ShortComplex A) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (_hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι)
    (_hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι)
    (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact)
    (hvH : ((ShortComplex.mk α β hαβ).map
      (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact)
    (hExt : (((ShortComplex.mk α β hαβ).map
      (v.mapHomologicalComplex (ComplexShape.up ℕ))).map
      (ComplexShape.embeddingUpNat.extendFunctor B)).ShortExact) :
    let T := (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      hS.singleTrianglePlus
    let U := DerivedCategory.triangleOfSES hExt
    (T.mor₃ ≫ (injectiveResolutionDerivedComparison v IA)⟦(1 : ℤ)⟧' =
      injectiveResolutionDerivedComparison v IC ≫ U.mor₃) := by
  let H := resolutionShortComplex IA IB IC α β hαβ
  have hH : (H.map (CochainComplex.plus A).ι).ShortExact :=
    extension_shortExact (ShortComplex.mk α β hαβ)
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr _hH)
  let e : ((H.map (CochainComplex.plus A).ι).map
      (v.mapHomologicalComplex (.up ℤ))) ≅
      (((ShortComplex.mk α β hαβ).map (v.mapHomologicalComplex (.up ℕ))).map
        (ComplexShape.embeddingUpNat.extendFunctor B)) :=
    ShortComplex.isoMk
      (IA.cocomplex.mapExtendIso ComplexShape.embeddingUpNat v)
      (IB.cocomplex.mapExtendIso ComplexShape.embeddingUpNat v)
      (IC.cocomplex.mapExtendIso ComplexShape.embeddingUpNat v)
      (by ext i; exact (HomologicalComplex.mapExtensIso_hom_f_naturality _ _ _ _).symm)
      (by ext i; exact (HomologicalComplex.mapExtensIso_hom_f_naturality _ _ _ _).symm)
  have hV := ShortComplex.shortExact_of_iso e.symm (extension_shortExact _ hvH)
  have haug := augmentation_boundary S hS IA IB IC α β hαβ _hιA _hιB hH
  have : ∀ n : ℤ, Injective ((resolutionPlus IA).obj.X n) := resolutionPlus_injective IA
  have : ∀ n : ℤ, Injective ((resolutionPlus IC).obj.X n) := resolutionPlus_injective IC
  have : ∀ n : ℤ, Injective (H.X₁.obj.X n) := resolutionPlus_injective IA
  have : ∀ n : ℤ, Injective (H.X₂.obj.X n) := resolutionPlus_injective IB
  have : ∀ n : ℤ, Injective (H.X₃.obj.X n) := resolutionPlus_injective IC
  have hunit := rightDerived_injectiveComplex_boundary v H hH hV
  have hshift (n : ℤ) :
      (Functor.commShiftIso v.rightDerivedFunctorPlus
        (self := v.instCommShiftPlusRightDerivedFunctorPlusInt) n).hom =
      (v.rightDerivedFunctorPlus.commShiftIso n).hom := by
    apply Functor.rightDerived_ext _
      (Functor.IsRightDerivedFunctor.precomposeShiftNatTrans _ v.rightDerivedFunctorPlusUnith n)
      (HomotopyCategory.Plus.quasiIso A)
    refine NatTrans.ext (funext fun K ↦ ?_)
    have h₁ := by
      letI := v.instCommShiftPlusRightDerivedFunctorPlusInt
      exact NatTrans.shift_app_comm v.rightDerivedFunctorPlusUnith n K
    have h₂ := NatTrans.shift_app_comm v.rightDerivedFunctorPlusUnith n K
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.IsRightDerivedFunctor.precomposeShiftNatTrans_app,
      Functor.commShiftIso_comp_hom_app, Category.assoc] using h₁.symm.trans h₂
  simp only [Functor.commShiftIso_comp_hom_app, hshift] at hunit
  have he := DerivedCategory.triangleOfSESδ_naturality hV hExt e.hom
  dsimp only
  rw [comparison_eq_unit v IA, comparison_eq_unit v IC]
  simp only [Functor.mapTriangle, Pretriangulated.Triangle.mk_mor₃, Functor.map_comp,
    Category.assoc]
  rw [← Functor.commShiftIso_hom_naturality_assoc,
    ← Functor.map_comp_assoc, haug, Functor.map_comp, Category.assoc]
  have hunit' :
      DerivedCategory.Plus.ι.map (v.rightDerivedFunctorPlus.map
          (boundedBelowSESBoundary H hH)) ≫
        DerivedCategory.Plus.ι.map
          ((v.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app
            (DerivedCategory.Plus.Q.obj H.X₁)) ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
          (v.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj H.X₁)) ≫
        (boundedBelowInjectiveComparison v H.X₁)⟦(1 : ℤ)⟧' =
      boundedBelowInjectiveComparison v H.X₃ ≫
        DerivedCategory.triangleOfSESδ hV := by
    simpa only [Functor.comp_map, Functor.commShiftIso_comp_hom_app, Category.assoc] using hunit
  simp only [Functor.comp_map, Functor.commShiftIso_comp_hom_app, Category.assoc]
  erw [reassoc_of% hunit', he]
  rfl

end CategoryTheory
