/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.Algebra.Homology.HomotopyCategory.KInjectives.KInjectiveReplacementTriangulated

/-!
# Right-derived transformations through an exact input functor

Source: Stacks Project, Derived Categories, Tags 05SE, 070Y and 070K; the exact-input
assembly in the DAG (blueprint: lem-sfb-exact-input-derived-transformation).

The unit equation characterizes the transformation without requiring the exact input
functor to preserve K-injectives. Its computation uses a second K-injective resolution.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uC vA vB vC wA wB wC

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wC} C]
  (E : A ⥤ B) (F : A ⥤ C) (G : B ⥤ C)
  [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [F.Additive] [G.Additive]
  (hA : ∀ K : CochainComplex A ℤ,
    ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  (hB : ∀ K : CochainComplex B ℤ,
    ∃ (I : CochainComplex B ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
  (β : F ⟶ E ⋙ G)

/-- The unit equation defining the exact-input comparison, written on the homotopy
category with the canonical localization and composition identifications inserted.
Source: the exact-input assembly from Stacks Tags 05SE and 070Y
(blueprint: lem-sfb-exact-input-derived-transformation). -/
def IsExactInputDerivedTransformation
    (τ : F.rightDerivedFunctorOfQuasiIsoResolutions hA ⟶
      E.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hB) : Prop :=
  ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA).app K ≫
        τ.app (DerivedCategory.Qh.obj K) ≫
        (G.rightDerivedFunctorOfQuasiIsoResolutions hB).map
          (E.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory β (ComplexShape.up ℤ)).app K ≫
          (mapHomotopyCategoryCompIso (Iso.refl (E ⋙ G)) (ComplexShape.up ℤ)).inv.app K) ≫
        (G.rightDerivedFunctorOfQuasiIsoResolutionsUnit hB).app
          ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)

private theorem commShift_of_precomp
    {D₀ D₁ D₂ : Type*} [Category D₀] [Category D₁] [Category D₂]
    [HasShift D₀ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
    (L : D₀ ⥤ D₁) [L.CommShift ℤ] [L.EssSurj]
    {U V : D₁ ⥤ D₂} [U.CommShift ℤ] [V.CommShift ℤ]
    (τ : U ⟶ V) [NatTrans.CommShift (whiskerLeft L τ) ℤ] :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro r
  let a := (U.commShiftIso r).hom ≫ whiskerRight τ (shiftFunctor _ r)
  let b := whiskerLeft (shiftFunctor _ r) τ ≫ (V.commShiftIso r).hom
  change a = b
  have h (X : D₀) : a.app (L.obj X) = b.app (L.obj X) := by
    have hh := NatTrans.congr_app (NatTrans.shift_comm (whiskerLeft L τ) r) X
    simp only [Functor.commShiftIso_comp_hom_app, NatTrans.comp_app,
      whiskerRight_app, whiskerLeft_app, Category.assoc] at hh
    rw [← τ.naturality_assoc] at hh
    exact (cancel_epi (U.map ((L.commShiftIso r).hom.app X))).mp hh
  ext X
  let e := L.objObjPreimageIso X
  apply (cancel_mono ((V ⋙ shiftFunctor _ r).map e.inv)).mp
  rw [← a.naturality, ← b.naturality, h]

private theorem commShift_cancel_left
    {D₀ D₁ : Type*} [Category D₀] [Category D₁]
    [HasShift D₀ ℤ] [HasShift D₁ ℤ]
    {U V W : D₀ ⥤ D₁} [U.CommShift ℤ] [V.CommShift ℤ] [W.CommShift ℤ]
    (η : U ⟶ V) (τ : V ⟶ W) [NatTrans.CommShift η ℤ]
    [NatTrans.CommShift (η ≫ τ) ℤ] [∀ X, Epi (η.app X)] :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro r
  ext X
  apply (cancel_epi (η.app (X⟦r⟧))).mp
  have hh := NatTrans.shift_app_comm (η ≫ τ) r X
  simpa only [NatTrans.comp_app, Functor.map_comp, Category.assoc,
    NatTrans.shift_app_comm_assoc, whiskerRight_app, whiskerLeft_app] using hh

omit [HasDerivedCategory A] in
include hA in
private theorem commShift_of_restriction
    (H₀ H₁ : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory C)
    [H₀.CommShift ℤ] [H₁.CommShift ℤ] (η : H₀ ⟶ H₁)
    (hr : NatTrans.CommShift
      (whiskerLeft (HomotopyCategory.KInjectives.ι (C := A)) η) ℤ)
    (hi : ∀ {K I : CochainComplex A ℤ} [I.IsKInjective]
      (s : K ⟶ I) [QuasiIso s],
      IsIso (H₁.map ((HomotopyCategory.quotient _ _).map s))) :
    NatTrans.CommShift η ℤ := by
  have := hr
  constructor
  intro r
  let a := (H₀.commShiftIso r).hom ≫ whiskerRight η (shiftFunctor _ r)
  let b := whiskerLeft (shiftFunctor _ r) η ≫ (H₁.commShiftIso r).hom
  change a = b
  ext K
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨I, s, hI, hs⟩ := hA K
  have := hI
  have := hs
  have hv := NatTrans.congr_app
    (NatTrans.shift_comm (whiskerLeft (HomotopyCategory.KInjectives.ι (C := A)) η) r)
      (HomotopyCategory.KInjectives.mk I)
  simp only [Functor.commShiftIso_comp_hom_app, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, Category.assoc] at hv
  rw [← η.naturality_assoc] at hv
  have hv' : a.app ((HomotopyCategory.quotient _ _).obj I) =
      b.app ((HomotopyCategory.quotient _ _).obj I) :=
    (cancel_epi (H₀.map
      (((HomotopyCategory.KInjectives.ι (C := A)).commShiftIso r).hom.app
        (HomotopyCategory.KInjectives.mk I)))).mp hv
  have : IsIso (H₁.map ((HomotopyCategory.quotient _ _).map s)) := hi s
  have : IsIso ((H₁ ⋙ shiftFunctor _ r).map
      ((HomotopyCategory.quotient _ _).map s)) := (shiftFunctor _ r).map_isIso _
  apply (cancel_mono
    ((H₁ ⋙ shiftFunctor _ r).map ((HomotopyCategory.quotient _ _).map s))).mp
  rw [← a.naturality, ← b.naturality, hv']

private theorem derived_shifts :
    ∃ SF : (F.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ,
      (fun [_sF : (F.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ] ↦
        NatTrans.CommShift (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA) ℤ ∧
        (F.rightDerivedFunctorOfQuasiIsoResolutions hA).IsTriangulated) (_sF := SF) := by
  classical
  let ι := HomotopyCategory.KInjectives.ι (C := A)
  let q := HomotopyCategory.KInjectives.Qh (C := A)
  let RF := F.rightDerivedFunctorOfQuasiIsoResolutions hA
  let η := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA
  let H := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have hq := HomotopyCategory.KInjectives.replacement_triangulated A hA
  have : q.IsEquivalence := hq.2.2.2.1
  have : ι.IsTriangulated := hq.2.2.1
  have : q.IsTriangulated := hq.2.2.2.2.1
  have hη : IsIso (whiskerLeft ι η) := by
    have : ∀ X, IsIso ((whiskerLeft ι η).app X) := by
      intro X
      obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
      exact F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hA I
    exact NatIso.isIso_of_isIso_app _
  let e : q ⋙ RF ≅ ι ⋙ H :=
    associator ι DerivedCategory.Qh RF ≪≫ (asIso (whiskerLeft ι η)).symm
  have : q.IsLocalization (MorphismProperty.isomorphisms _) :=
    Functor.IsLocalization.of_isEquivalence q _ le_rfl
  let : Localization.Lifting q (MorphismProperty.isomorphisms _) (ι ⋙ H) RF := ⟨e⟩
  let : RF.CommShift ℤ :=
    Functor.commShiftOfLocalization q (MorphismProperty.isomorphisms _) ℤ (ι ⋙ H) RF
  have he : NatTrans.CommShift e.hom ℤ := by
    exact NatTrans.commShift_iso_hom_of_localization q
      (MorphismProperty.isomorphisms _) ℤ (ι ⋙ H) RF
  have htri : RF.IsTriangulated := Functor.isTriangulated_of_precomp_iso e
  have hr : NatTrans.CommShift (whiskerLeft ι η) ℤ := by
    have heq : whiskerLeft ι η = e.inv ≫ (associator ι DerivedCategory.Qh RF).hom := by
      ext X
      simp [e]
    rw [heq]
    infer_instance
  refine ⟨inferInstance, ?_, htri⟩
  apply commShift_of_restriction hA H (DerivedCategory.Qh ⋙ RF) η hr
  intro K I _ s _
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map s)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ))
      ((HomotopyCategory.quotient _ _).map s)
        (by simpa [HomotopyCategory.quotient_map_mem_quasiIso_iff])
  exact RF.map_isIso _

private noncomputable def comparison_input :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        (E.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hB) :=
    whiskerRight (NatTrans.mapHomotopyCategory β (ComplexShape.up ℤ) ≫
      (mapHomotopyCategoryCompIso (Iso.refl (E ⋙ G)) (ComplexShape.up ℤ)).inv)
        DerivedCategory.Qh ≫
    (associator _ _ _).hom ≫
    whiskerLeft (E.mapHomotopyCategory (ComplexShape.up ℤ))
      (G.rightDerivedFunctorOfQuasiIsoResolutionsUnit hB) ≫
    (associator _ _ _).inv ≫
    whiskerRight E.mapDerivedCategoryFactorsh.inv
      (G.rightDerivedFunctorOfQuasiIsoResolutions hB) ≫
    (associator _ _ _).hom

private theorem comparison_exists_unique :
    ∃! τ : F.rightDerivedFunctorOfQuasiIsoResolutions hA ⟶
      E.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hB,
      IsExactInputDerivedTransformation E F G hA hB β τ := by
  let α := comparison_input E F G hB β
  obtain ⟨τ, hτ⟩ := (F.rightDerivedFunctorOfQuasiIsoResolutions_universal hA _).surjective α
  have fac (σ : F.rightDerivedFunctorOfQuasiIsoResolutions hA ⟶
      E.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hB) :
      IsExactInputDerivedTransformation E F G hA hB β σ ↔
      F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA ≫
        whiskerLeft DerivedCategory.Qh σ = α := by
    constructor
    · intro hσ
      ext K
      apply (cancel_mono ((G.rightDerivedFunctorOfQuasiIsoResolutions hB).map
        (E.mapDerivedCategoryFactorsh.hom.app K))).mp
      simpa [α, comparison_input, Functor.map_comp, Category.assoc] using hσ K
    · intro hσ K
      have hh := NatTrans.congr_app hσ K
      have hh' := congrArg (fun f ↦ f ≫
        (G.rightDerivedFunctorOfQuasiIsoResolutions hB).map
          (E.mapDerivedCategoryFactorsh.hom.app K)) hh
      simpa [α, comparison_input, Functor.map_comp, Category.assoc] using hh'
  refine ⟨τ, (fac τ).2 hτ, ?_⟩
  intro σ hσ
  apply (F.rightDerivedFunctorOfQuasiIsoResolutions_universal hA _).injective
  exact ((fac σ).1 hσ).trans hτ.symm

private noncomputable def complex_unit :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions hA :=
  whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
    (DerivedCategory.quotientCompQhIso C).inv ≫
  whiskerLeft (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA) ≫
  whiskerRight (DerivedCategory.quotientCompQhIso A).hom
    (F.rightDerivedFunctorOfQuasiIsoResolutions hA)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem complex_fac
    (τ : F.rightDerivedFunctorOfQuasiIsoResolutions hA ⟶
      E.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hB)
    (hτ : IsExactInputDerivedTransformation E F G hA hB β τ)
    (K : CochainComplex A ℤ) :
    (complex_unit F hA).app K ≫ τ.app (DerivedCategory.Q.obj K) ≫
      (G.rightDerivedFunctorOfQuasiIsoResolutions hB).map
        (E.mapDerivedCategoryFactors.hom.app K) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app K ≫
          (mapHomologicalComplexCompIso (Iso.refl (E ⋙ G))
            (ComplexShape.up ℤ)).inv.app K) ≫
      (complex_unit G hB).app ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  let π := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let RG := G.rightDerivedFunctorOfQuasiIsoResolutions hB
  let φ := (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app K ≫
    (mapHomologicalComplexCompIso (Iso.refl (E ⋙ G)) (ComplexShape.up ℤ)).inv.app K
  have ht := hτ (π.obj K)
  rw [mapDerivedCategoryFactorsh_hom_app] at ht
  have h1 : DerivedCategory.Qh.map
      ((E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have h2 : (NatTrans.mapHomotopyCategory β (ComplexShape.up ℤ)).app (π.obj K) ≫
      (mapHomotopyCategoryCompIso (Iso.refl (E ⋙ G)) (ComplexShape.up ℤ)).inv.app (π.obj K) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ := rfl
  rw [h1, h2] at ht
  erw [Category.comp_id] at ht
  have ht' := congrArg (· ≫ RG.map ((DerivedCategory.quotientCompQhIso B).hom.app
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ht
  simp only [Category.assoc] at ht'
  erw [← Functor.map_comp] at ht'
  simp only [Category.assoc, Iso.inv_hom_id_app] at ht'
  erw [Category.comp_id] at ht'
  dsimp only [complex_unit, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [Category.assoc, Category.assoc, τ.naturality_assoc, Functor.comp_map,
    ← Functor.map_comp]
  erw [ht']
  exact (DerivedCategory.quotientCompQhIso_inv_naturality_assoc φ _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E] in
private theorem complex_beta_shifts :
    NatTrans.CommShift
      (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ) ≫
        (mapHomologicalComplexCompIso (Iso.refl (E ⋙ G))
          (ComplexShape.up ℤ)).inv) ℤ := by
  constructor
  intro r
  ext K i
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.commShiftIso_comp_hom_app]
  simp [mapHomologicalComplex_commShiftIso_hom_app_f,
    mapHomologicalComplexCompIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E] in
private theorem homotopy_beta_shifts :
    NatTrans.CommShift
      (NatTrans.mapHomotopyCategory β (ComplexShape.up ℤ) ≫
        (mapHomotopyCategoryCompIso (Iso.refl (E ⋙ G))
          (ComplexShape.up ℤ)).inv) ℤ := by
  let γ := NatTrans.mapHomotopyCategory β (ComplexShape.up ℤ) ≫
    (mapHomotopyCategoryCompIso (Iso.refl (E ⋙ G)) (ComplexShape.up ℤ)).inv
  let δ := NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ) ≫
    (mapHomologicalComplexCompIso (Iso.refl (E ⋙ G)) (ComplexShape.up ℤ)).inv
  have : NatTrans.CommShift δ ℤ := complex_beta_shifts E F G β
  let πA := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let πC := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  have heq : whiskerLeft πA γ =
      (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ≫
      whiskerRight δ πC ≫
      (associator _ _ _).hom ≫
      whiskerLeft (E.mapHomologicalComplex (ComplexShape.up ℤ))
        (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv ≫
      (associator _ _ _).inv ≫
      whiskerRight (E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv
        (G.mapHomotopyCategory (ComplexShape.up ℤ)) ≫
      (associator _ _ _).hom := by
    ext K
    dsimp [γ, δ, πA, πC, NatTrans.mapHomotopyCategory, Quotient.natTransLift,
      mapHomotopyCategoryFactors, mapHomotopyCategoryCompIso, Quotient.natIsoLift,
      mapHomotopyCategory, HomotopyCategory.quotient, Quotient.functor, Quotient.lift,
      Quotient.category, Quotient.comp]
    simp only [Category.id_comp, Category.comp_id]
    change (HomotopyCategory.quotient C _).map
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app K) ≫
        (HomotopyCategory.quotient C _).map
          ((mapHomologicalComplexCompIso (Iso.refl (E ⋙ G))
            (ComplexShape.up ℤ)).inv.app K) =
      (HomotopyCategory.quotient C _).map (δ.app K) ≫
        (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (𝟙 ((HomotopyCategory.quotient B _).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
    erw [(G.mapHomotopyCategory (ComplexShape.up ℤ)).map_id]
    simp only [δ, NatTrans.comp_app, Functor.map_comp]
    with_unfolding_all exact (Category.comp_id _).symm
  have : NatTrans.CommShift (whiskerLeft πA γ) ℤ := by
    rw [heq]
    infer_instance
  exact commShift_of_precomp πA γ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem comparison_shifts
    [(F.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ]
    [(G.rightDerivedFunctorOfQuasiIsoResolutions hB).CommShift ℤ]
    [NatTrans.CommShift (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA) ℤ]
    [NatTrans.CommShift (G.rightDerivedFunctorOfQuasiIsoResolutionsUnit hB) ℤ]
    (τ : F.rightDerivedFunctorOfQuasiIsoResolutions hA ⟶
      E.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hB)
    (hτ : IsExactInputDerivedTransformation E F G hA hB β τ) :
    NatTrans.CommShift τ ℤ := by
  let α := comparison_input E F G hB β
  have : NatTrans.CommShift
      (NatTrans.mapHomotopyCategory β (ComplexShape.up ℤ) ≫
        (mapHomotopyCategoryCompIso (Iso.refl (E ⋙ G))
          (ComplexShape.up ℤ)).inv) ℤ := homotopy_beta_shifts E F G β
  have hα : NatTrans.CommShift α ℤ := by
    dsimp only [α, comparison_input]
    infer_instance
  have hf : F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA ≫
      whiskerLeft DerivedCategory.Qh τ = α := by
    ext K
    apply (cancel_mono ((G.rightDerivedFunctorOfQuasiIsoResolutions hB).map
      (E.mapDerivedCategoryFactorsh.hom.app K))).mp
    simpa [α, comparison_input, Functor.map_comp, Category.assoc] using hτ K
  let ι := HomotopyCategory.KInjectives.ι (C := A)
  have hq := HomotopyCategory.KInjectives.replacement_triangulated A hA
  have : (HomotopyCategory.KInjectives.Qh (C := A)).IsEquivalence := hq.2.2.2.1
  let η := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA
  have : ∀ X, IsIso ((whiskerLeft ι η).app X) := by
    intro X
    obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    exact F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hA I
  let q := HomotopyCategory.KInjectives.Qh (C := A)
  let u : ι ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions hA :=
    whiskerLeft ι η ≫ (associator ι DerivedCategory.Qh _).inv
  have : NatTrans.CommShift u ℤ := by dsimp only [u]; infer_instance
  have : ∀ X, Epi (u.app X) := by
    intro X
    change Epi ((whiskerLeft ι η).app X ≫ 𝟙 _)
    simpa only [Category.comp_id] using
      (inferInstance : Epi ((whiskerLeft ι η).app X))
  have heq : u ≫ whiskerLeft q τ =
      whiskerLeft ι α ≫ (associator ι DerivedCategory.Qh _).inv := by
    rw [← hf]
    ext X
    simp [u, η, q, ι, HomotopyCategory.KInjectives.Qh]
  have : NatTrans.CommShift (u ≫ whiskerLeft q τ) ℤ := by
    rw [heq]
    have := hα
    infer_instance
  have := commShift_cancel_left u (whiskerLeft q τ)
  exact commShift_of_precomp q τ

private instance complex_unit_isIso (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((complex_unit F hA).app I) := by
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hA I
  dsimp [complex_unit]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem objIso_hom
    {K I : CochainComplex A ℤ} [I.IsKInjective] (s : K ⟶ I) [QuasiIso s] :
    (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hA s).hom =
      (F.rightDerivedFunctorOfQuasiIsoResolutions hA).map (DerivedCategory.Q.map s) ≫
        CategoryTheory.inv ((complex_unit F hA).app I) := by
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hA I
  have : IsIso ((complex_unit F hA).app I) := by
    dsimp [complex_unit]
    infer_instance
  apply (cancel_mono ((complex_unit F hA).app I)).mp
  simp only [rightDerivedFunctorOfQuasiIsoResolutionsObjIso, complex_unit,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  simp only [← Functor.map_comp,
    Iso.inv_hom_id_app, Functor.map_id,
    Iso.hom_inv_id_app_assoc, IsIso.inv_hom_id_assoc, Category.comp_id]

private theorem comparison_computation
    (τ : F.rightDerivedFunctorOfQuasiIsoResolutions hA ⟶
      E.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hB)
    (hτ : IsExactInputDerivedTransformation E F G hA hB β τ)
    (K I : CochainComplex A ℤ) [I.IsKInjective] (s : K ⟶ I) [QuasiIso s]
    (H : CochainComplex B ℤ) [H.IsKInjective]
    (j : (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ H) [QuasiIso j] :
    (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hA s).inv ≫
        τ.app (DerivedCategory.Q.obj K) ≫
        (G.rightDerivedFunctorOfQuasiIsoResolutions hB).map
          (E.mapDerivedCategoryFactors.hom.app K) ≫
        (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hB
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map s ≫ j)).hom =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I ≫
          (mapHomologicalComplexCompIso (Iso.refl (E ⋙ G))
            (ComplexShape.up ℤ)).inv.app I ≫
          (G.mapHomologicalComplex (ComplexShape.up ℤ)).map j) := by
  let RF := F.rightDerivedFunctorOfQuasiIsoResolutions hA
  let RG := G.rightDerivedFunctorOfQuasiIsoResolutions hB
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hA I
  have := G.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hB H
  have huI : IsIso ((complex_unit F hA).app I) := by
    dsimp [complex_unit]
    infer_instance
  have huH : IsIso ((complex_unit G hB).app H) := by
    dsimp [complex_unit]
    infer_instance
  have hf : (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hA s).inv ≫
      RF.map (DerivedCategory.Q.map s) = (complex_unit F hA).app I := by
    apply (cancel_epi (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hA s).hom).mp
    rw [Iso.hom_inv_id_assoc]
    rw [objIso_hom]
    simp [RF]
  rw [objIso_hom G hB]
  simp only [Functor.map_comp, Category.assoc]
  rw [← RG.map_comp_assoc, ← E.mapDerivedCategoryFactors_hom_naturality,
    RG.map_comp_assoc]
  have hn := τ.naturality_assoc (DerivedCategory.Q.map s)
    (RG.map (E.mapDerivedCategoryFactors.hom.app I) ≫
      RG.map (DerivedCategory.Q.map j) ≫ CategoryTheory.inv ((complex_unit G hB).app H))
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  change (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hA s).inv ≫
      RF.map (DerivedCategory.Q.map s) ≫ _ = _
  rw [← Category.assoc, hf]
  have hc := complex_fac E F G hA hB β τ hτ I
  have hc' := congrArg (fun f ↦ f ≫ RG.map (DerivedCategory.Q.map j) ≫
    CategoryTheory.inv ((complex_unit G hB).app H)) hc
  simp only [Category.assoc] at hc'
  rw [hc']
  have hj := (complex_unit G hB).naturality_assoc j
    (CategoryTheory.inv ((complex_unit G hB).app H))
  dsimp only [Functor.comp_map] at hj
  rw [← hj]
  simp [Functor.map_comp, Category.assoc]

set_option linter.unusedVariables false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unique exact-input transformation, its two-resolution computation and its
compatibility with all signed shifts and distinguished triangles. The existential shift
structures are normalized by commutation of the computation units with the standard
signed shifts; thus they are the canonical structures on the chosen universal pairs.
Source: Stacks Tags 05SE, 070Y and 070K, exact-input assembly in the DAG
(blueprint: lem-sfb-exact-input-derived-transformation).

Proof:
1. Restrict each computation unit to K-injectives, where it is invertible. The
   K-injective localization is an equivalence. Descend shifts along this equivalence
   using the inverse restricted unit, and transport triangulatedness along the same
   comparison. Naturality along a K-injective resolution extends unit compatibility
   with shifts from K-injectives to all homotopy objects.
2. Compose beta on homotopy categories with the G-unit and the inverse exact-input
   factorization. The universal bijection for the chosen F-pair gives a unique tau
   satisfying the displayed unit equation.
3. Write the units on complexes through the quotient identifications. Naturality of
   tau at Qs, the unit equation at I, and naturality of the G-unit at j give the
   two-resolution formula after cancelling the invertible units at I and H. Every
   choice computes the same tau, so no separate change-of-resolution maps are needed.
4. Termwise beta commutes with the signed shifts degreewise. Descend this fact to
   homotopy categories using the quotient factorization isomorphisms. Restrict the
   defining equation of tau to K-injectives and cancel the invertible F-unit to prove
   shift compatibility there. Essential surjectivity extends it to all derived objects.
5. The triangle morphism has tau as its three components. Its first two squares are
   naturality; the third is naturality at the connecting arrow followed by the shift
   equation for r = 1. -/
theorem exists_unique_exactInputDerivedTransformation :
    ∃ SF : (F.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ,
    ∃ SG : (G.rightDerivedFunctorOfQuasiIsoResolutions hB).CommShift ℤ,
      (fun [sF : (F.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ]
        [sG : (G.rightDerivedFunctorOfQuasiIsoResolutions hB).CommShift ℤ] ↦
        NatTrans.CommShift (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA) ℤ ∧
        NatTrans.CommShift (G.rightDerivedFunctorOfQuasiIsoResolutionsUnit hB) ℤ ∧
        (F.rightDerivedFunctorOfQuasiIsoResolutions hA).IsTriangulated ∧
        (G.rightDerivedFunctorOfQuasiIsoResolutions hB).IsTriangulated ∧
        ∃ τ : F.rightDerivedFunctorOfQuasiIsoResolutions hA ⟶
            E.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hB,
          IsExactInputDerivedTransformation E F G hA hB β τ ∧
          (∀ τ' : F.rightDerivedFunctorOfQuasiIsoResolutions hA ⟶
              E.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hB,
            IsExactInputDerivedTransformation E F G hA hB β τ' → τ' = τ) ∧
          (∀ (K I : CochainComplex A ℤ) [I.IsKInjective]
            (s : K ⟶ I) [QuasiIso s]
            (H : CochainComplex B ℤ) [H.IsKInjective]
            (j : (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ H) [QuasiIso j],
            (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hA s).inv ≫
                τ.app (DerivedCategory.Q.obj K) ≫
                (G.rightDerivedFunctorOfQuasiIsoResolutions hB).map
                  (E.mapDerivedCategoryFactors.hom.app K) ≫
                (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hB
                  ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map s ≫ j)).hom =
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I ≫
                  (mapHomologicalComplexCompIso (Iso.refl (E ⋙ G))
                    (ComplexShape.up ℤ)).inv.app I ≫
                  (G.mapHomologicalComplex (ComplexShape.up ℤ)).map j)) ∧
          (∀ (r : ℤ) (X : DerivedCategory A),
            τ.app (X⟦r⟧) ≫
                ((E.mapDerivedCategory ⋙
                  G.rightDerivedFunctorOfQuasiIsoResolutions hB).commShiftIso r).hom.app X =
              ((F.rightDerivedFunctorOfQuasiIsoResolutions hA).commShiftIso r).hom.app X ≫
                (τ.app X)⟦r⟧') ∧
          (∀ T : Triangle (DerivedCategory A), T ∈ distTriang (DerivedCategory A) →
            ∃ t : (F.rightDerivedFunctorOfQuasiIsoResolutions hA).mapTriangle.obj T ⟶
                (E.mapDerivedCategory ⋙
                  G.rightDerivedFunctorOfQuasiIsoResolutions hB).mapTriangle.obj T,
              t.hom₁ = τ.app T.obj₁ ∧ t.hom₂ = τ.app T.obj₂ ∧ t.hom₃ = τ.app T.obj₃))
        (sF := SF) (sG := SG) := by
  obtain ⟨SF, hSF, hTF⟩ := derived_shifts F hA
  obtain ⟨SG, hSG, hTG⟩ := derived_shifts G hB
  let := SF
  let := SG
  have := hSF
  have := hSG
  have := hTF
  have := hTG
  obtain ⟨τ, hτ, huniq⟩ := comparison_exists_unique E F G hA hB β
  have := comparison_shifts E F G hA hB β τ hτ
  refine ⟨SF, SG, hSF, hSG, hTF, hTG, τ, hτ, huniq, ?_, ?_, ?_⟩
  · intro K I _ s _ H _ j _
    exact comparison_computation E F G hA hB β τ hτ K I s H j
  · intro r X
    exact (NatTrans.shift_app_comm τ r X).symm
  · intro T _
    refine ⟨{ hom₁ := τ.app T.obj₁
              hom₂ := τ.app T.obj₂
              hom₃ := τ.app T.obj₃
              comm₁ := τ.naturality T.mor₁
              comm₂ := τ.naturality T.mor₂
              comm₃ := ?_ }, rfl, rfl, rfl⟩
    simp only [Functor.mapTriangle_obj, Triangle.mk_mor₃, Category.assoc]
    rw [NatTrans.shift_app_comm, ← τ.naturality_assoc]

end CategoryTheory.Functor
