/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!
# Canonical tensor comparison for condensed module inverse image

Source: Stacks Project, Tags 03EL and 0G7D; the totalization and K-flat descent in
steps 3--7 of the open/closed internal-Hom calculation
(auxiliary; not a blueprint node).

The coequalizer equation determines the ordinary comparison. The equation on every
summand of the total tensor complex then determines its unbounded derived comparison.
The choices below are from unique, fully normalized objects, never arbitrary isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

private theorem existsUnique_mapModComapTensorComparison
    {C : Type w₁} {D : Type w₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    [MonoidalCategory D] [BraidedCategory D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
    {R : C} [MonObj R] [IsCommMonObj R] {S : D} [MonObj S] [IsCommMonObj S]
    (ψ : S ⟶ F.obj R) [IsMonHom ψ] [IsIso ψ] (M N : Mod C R) :
    let r := F.mapMod R ⋙ Mod.comap ψ
    ∃! e : r.obj (M ⊗ N) ≅ r.obj M ⊗ r.obj N,
      Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) ≫ e.hom.hom =
        Mod.tensorObjπ (r.obj M) (r.obj N) := by
  let r := F.mapMod R ⋙ Mod.comap ψ
  let e := Mod.comapTensorIso ψ ((F.mapMod R).obj M) ((F.mapMod R).obj N) ≪≫
    (Mod.comap ψ).mapIso (F.mapModTensorIso M N)
  have he : Mod.tensorObjπ (r.obj M) (r.obj N) ≫ e.hom.hom =
      Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) := by
    dsimp only [r, Functor.comp_obj, e, Iso.trans_hom, Functor.mapIso_hom,
      Mod.comp_hom']
    rw [← Category.assoc, Mod.tensorπ_comapTensorIso_hom_hom]
    exact F.tensorπ_mapModTensorIso_hom_hom M N
  have hn : Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) ≫
      e.inv.hom = Mod.tensorObjπ (r.obj M) (r.obj N) := by
    rw [← Category.assoc, ← he, Category.assoc]
    change _ ≫ (e.hom ≫ e.inv).hom = _
    simp only [e.hom_inv_id, Mod.id_hom', Category.comp_id]
  refine ⟨e.symm, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Mod.hom_ext
  apply (cancel_epi e.hom.hom).mp
  apply (cancel_epi (Mod.tensorObjπ (r.obj M) (r.obj N))).mp
  simp only [← Category.assoc]
  rw [he]
  simpa only [r, Iso.symm_hom, Category.assoc] using he'.trans hn.symm

section ExactTensor

variable {C : Type w₁} {D : Type w₂}
  [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.IsLeftAdjoint] [F.Monoidal]

/-- The comparison family for the termwise derived functor of an exact functor.
Source: Stacks Tag 0G7D
(auxiliary; not a blueprint node).
Keeping the tensor structure inside this generic definition avoids repeatedly unfolding
specialized sheaf monoidal instances when checking a comparison family. -/
def ExactDerivedTensorComparisonFamily :=
  ∀ K M : DerivedCategory C,
    F.mapDerivedCategory.obj (K ⊗ M) ≅
      F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj M

/-- Naturality and the total-complex square for a specified ordinary comparison.
Source: Stacks Tags 06YL and 0G7D
(auxiliary; not a blueprint node).
This is the generic form of `SupportDerivedTensorNormalization`: tensor morphisms
are written as the two maps of the curried tensor functor. -/
def ExactDerivedTensorNormalization
    (d : ∀ A B : CochainComplex C ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (A ⊗ B) ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj A ⊗
          (F.mapHomologicalComplex (.up ℤ)).obj B)
    (e : ExactDerivedTensorComparisonFamily F) : Prop :=
  (∀ (K K' M M' : DerivedCategory C) (a : K ⟶ K') (b : M ⟶ M'),
    F.mapDerivedCategory.map
        (((curriedTensor _).map a).app M ≫ ((curriedTensor _).obj K').map b) ≫
        (e K' M').hom =
      (e K M).hom ≫
        ((curriedTensor _).map (F.mapDerivedCategory.map a)).app
          (F.mapDerivedCategory.obj M) ≫
        ((curriedTensor _).obj (F.mapDerivedCategory.obj K')).map
          (F.mapDerivedCategory.map b)) ∧
  ∀ A B : CochainComplex C ℤ,
    F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q A B) ≫
      F.mapDerivedCategoryFactors.hom.app (A ⊗ B) ≫ DerivedCategory.Q.map (d A B) =
    (e (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)).hom ≫
      (((curriedTensor _).map (F.mapDerivedCategoryFactors.hom.app A)).app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj B)) ≫
        ((curriedTensor _).obj
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj A))).map
            (F.mapDerivedCategoryFactors.hom.app B)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj A)
        ((F.mapHomologicalComplex (.up ℤ)).obj B)

private noncomputable def exactDerivedTensorCandidate [F.PreservesFlat] :
    ∀ K M : DerivedCategory C,
      F.mapDerivedCategory.obj (K ⊗ M) ≅
        F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj M := by
  let e := F.leftDerivedFunctorIsoMapDerivedCategory
  exact fun K M ↦ e.symm.app (K ⊗ M) ≪≫
    asIso ((F.leftDerivedTensorComparison.app K).app M) ≪≫
    (tensorIso (e.app K) (e.app M))

private theorem exactDerivedTensorCandidate_naturality [F.PreservesFlat]
    (K K' M M' : DerivedCategory C)
    (a : K ⟶ K') (b : M ⟶ M') :
    F.mapDerivedCategory.map (a ⊗ₘ b) ≫
        (exactDerivedTensorCandidate F K' M').hom =
      (exactDerivedTensorCandidate F K M).hom ≫
        (F.mapDerivedCategory.map a ⊗ₘ
          F.mapDerivedCategory.map b) := by
  let e := F.leftDerivedFunctorIsoMapDerivedCategory
  change F.mapDerivedCategory.map (a ⊗ₘ b) ≫
      (e.inv.app (K' ⊗ M') ≫ (F.leftDerivedTensorComparison.app K').app M' ≫
        (e.hom.app K' ⊗ₘ e.hom.app M')) =
    (e.inv.app (K ⊗ M) ≫ (F.leftDerivedTensorComparison.app K).app M ≫
        (e.hom.app K ⊗ₘ e.hom.app M)) ≫
      (F.mapDerivedCategory.map a ⊗ₘ F.mapDerivedCategory.map b)
  rw [e.inv.naturality_assoc, F.leftDerivedTensorComparison_naturality_tensorHom_assoc]
  simp only [Category.assoc, tensorHom_comp_tensorHom, e.hom.naturality]

private theorem exactDerivedTensorCandidate_homotopy [F.PreservesFlat]
    (A B : HomotopyCategory C (.up ℤ)) :
    (exactDerivedTensorCandidate F (DerivedCategory.Qh.obj A)
        (DerivedCategory.Qh.obj B)).hom ≫
      (F.mapDerivedCategoryFactorsh.hom.app A ⊗ₘ F.mapDerivedCategoryFactorsh.hom.app B) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((F.mapHomotopyCategory (.up ℤ)).obj A)
        ((F.mapHomotopyCategory (.up ℤ)).obj B) =
      F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫
        F.mapDerivedCategoryFactorsh.hom.app (A ⊗ B) ≫ DerivedCategory.Qh.map
          (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app A).app B) := by
  let e := F.leftDerivedFunctorIsoMapDerivedCategory
  change (e.inv.app _ ≫ (F.leftDerivedTensorComparison.app _).app _ ≫
      (e.hom.app _ ⊗ₘ e.hom.app _)) ≫ _ ≫ _ = _
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, e,
    F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac]
  rw [F.leftDerivedTensorComparison_app_app_comp_tensorHom]
  rw [← e.inv.naturality_assoc]
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac]
  simp only [e, Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem derivedLocalizationTensor_eq (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q) := by
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ (DerivedCategory.Qh (C := C)).map (𝟙 _)) ≫
    𝟙 _ = _
  rw [(DerivedCategory.Qh (C := C)).map_id]
  simp only [id_tensorHom_id, Category.id_comp, Category.comp_id]
  rfl

private theorem exactDerivedTensorCandidate_complex [F.PreservesFlat]
    (A B : CochainComplex C ℤ) :
    (exactDerivedTensorCandidate F (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B)).hom ≫
      (F.mapDerivedCategoryFactors.hom.app A ⊗ₘ F.mapDerivedCategoryFactors.hom.app B) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj A)
        ((F.mapHomologicalComplex (.up ℤ)).obj B) =
      F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q A B) ≫
        F.mapDerivedCategoryFactors.hom.app (A ⊗ B) ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorComparison
            (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) A B) := by
  have h := exactDerivedTensorCandidate_homotopy F
    ((HomotopyCategory.quotient C (.up ℤ)).obj A)
    ((HomotopyCategory.quotient C (.up ℤ)).obj B)
  have hf (A : CochainComplex C ℤ) :
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj A) =
        F.mapDerivedCategoryFactors.hom.app A := by
    rw [F.mapDerivedCategoryFactorsh_hom_app]
    change F.mapDerivedCategory.map (𝟙 _) ≫
      F.mapDerivedCategoryFactors.hom.app A ≫ 𝟙 _ ≫
        (DerivedCategory.Qh (C := D)).map (𝟙 _) = _
    rw [F.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := D)).map_id]
    simp only [Category.id_comp]
    exact Category.comp_id _
  change (exactDerivedTensorCandidate F (DerivedCategory.Q.obj A)
      (DerivedCategory.Q.obj B)).hom ≫
      (F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C (.up ℤ)).obj A) ⊗ₘ
        F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C (.up ℤ)).obj B)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient D (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj A))
        ((HomotopyCategory.quotient D (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj B)) =
      F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj A)
        ((HomotopyCategory.quotient C (.up ℤ)).obj B)) ≫
      F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj (A ⊗ B)) ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorComparison
        (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) A B) at h
  rw [derivedLocalizationTensor_eq, derivedLocalizationTensor_eq]
  simpa only [hf] using h

private theorem exactDerivedTensorCandidate_unique [F.PreservesFlat]
    (e : ∀ K M : DerivedCategory C,
      F.mapDerivedCategory.obj (K ⊗ M) ≅
        F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj M)
    (hn : ∀ (K K' M M' : DerivedCategory C) (a : K ⟶ K') (b : M ⟶ M'),
      F.mapDerivedCategory.map (a ⊗ₘ b) ≫ (e K' M').hom =
        (e K M).hom ≫ (F.mapDerivedCategory.map a ⊗ₘ F.mapDerivedCategory.map b))
    (hs : ∀ A B : CochainComplex C ℤ,
      (e (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)).hom ≫
        (F.mapDerivedCategoryFactors.hom.app A ⊗ₘ F.mapDerivedCategoryFactors.hom.app B) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj A)
          ((F.mapHomologicalComplex (.up ℤ)).obj B) =
        F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q A B) ≫
          F.mapDerivedCategoryFactors.hom.app (A ⊗ B) ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorComparison
              (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) A B)) :
    e = exactDerivedTensorCandidate F := by
  have heq (A B : CochainComplex C ℤ)
      (hB : (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
        ((HomotopyCategory.quotient D (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj B))) :
      (e (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)).hom =
        (exactDerivedTensorCandidate F (DerivedCategory.Q.obj A)
          (DerivedCategory.Q.obj B)).hom := by
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj A)
        ((F.mapHomologicalComplex (.up ℤ)).obj B)) := by
      rw [derivedLocalizationTensor_eq]
      exact Functor.isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hB
    apply (cancel_mono
      ((F.mapDerivedCategoryFactors.hom.app A ⊗ₘ F.mapDerivedCategoryFactors.hom.app B) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj A)
          ((F.mapHomologicalComplex (.up ℤ)).obj B))).mp
    simpa only [Category.assoc] using
      (hs A B).trans (exactDerivedTensorCandidate_complex F A B).symm
  funext K M
  let A := DerivedCategory.Q.objPreimage K
  let a := DerivedCategory.Q.objObjPreimageIso K
  let R := (inferInstance : Abelian.HasFunctorialFlatResolution C).some
  let B := R.reduced.resolutionFunctor.obj (DerivedCategory.Q.objPreimage M)
  let b : DerivedCategory.Q.obj B ≅ M :=
    asIso (DerivedCategory.Q.map
      (R.reduced.resolutionNatTrans.app (DerivedCategory.Q.objPreimage M))) ≪≫
      DerivedCategory.Q.objObjPreimageIso M
  have hB : (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
      ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj B)) :=
    F.kFlatMap_quotient_obj_resolutionFunctor_obj R.reduced _
  apply Iso.ext
  apply (cancel_epi (F.mapDerivedCategory.map (a.hom ⊗ₘ b.hom))).mp
  rw [hn _ _ _ _ a.hom b.hom,
    exactDerivedTensorCandidate_naturality F _ _ _ _ a.hom b.hom, heq A B hB]

private theorem existsUnique_exactDerivedTensorComparison [F.PreservesFlat]
    (d : ∀ A B : CochainComplex C ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (A ⊗ B) ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj A ⊗
          (F.mapHomologicalComplex (.up ℤ)).obj B)
    (hd : ∀ A B, d A B = HomologicalComplex.mapBifunctorComparison
      (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) A B) :
    ∃! e : ExactDerivedTensorComparisonFamily F, ExactDerivedTensorNormalization F d e := by
  refine ⟨exactDerivedTensorCandidate F, ⟨?_, ?_⟩, ?_⟩
  · intro K K' M M' a b
    simpa only [curriedTensor_map_app, curriedTensor_obj_map,
      curriedTensor_obj_obj, Functor.comp_obj, MonoidalCategory.tensorHom_def,
      Category.assoc] using exactDerivedTensorCandidate_naturality F K K' M M' a b
  · intro A B
    simpa only [hd, curriedTensor_map_app, curriedTensor_obj_map,
      curriedTensor_obj_obj, Functor.comp_obj, MonoidalCategory.tensorHom_def,
      Category.assoc] using (exactDerivedTensorCandidate_complex F A B).symm
  · intro e he
    apply exactDerivedTensorCandidate_unique F e
    · intro K K' M M' a b
      simpa only [curriedTensor_map_app, curriedTensor_obj_map,
        curriedTensor_obj_obj, Functor.comp_obj, MonoidalCategory.tensorHom_def,
        Category.assoc] using he.1 K K' M M' a b
    · intro A B
      simpa only [hd, curriedTensor_map_app, curriedTensor_obj_map,
        curriedTensor_obj_obj, Functor.comp_obj, MonoidalCategory.tensorHom_def,
        Category.assoc] using (he.2 A B).symm

end ExactTensor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Small colimits for the total tensor complexes, obtained by universe shrinking.
Source: Stacks Tag 06YL (auxiliary; not a blueprint node). -/
noncomputable instance supportModules_smallColimits (X : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (supportModules Λ X) :=
  hasColimitsOfSizeShrink (supportModules Λ X)

/-- Direct small-diagram colimits, using exactly the existing shrunken colimit instance.
Source: Stacks Tag 06YL (auxiliary; not a blueprint node). -/
instance (priority := 10000) supportModules_smallDiagramColimit
    (X : Scheme.{u}) {J : Type} [Category.{0} J] (D : J ⥤ supportModules Λ X) :
    HasColimit D :=
  (supportModules_smallColimits Λ X).has_colimits_of_shape J |>.has_colimit D

/-- Existence of the coproducts defining total tensor, with no search for larger colimits.
Source: Stacks Tag 06YL (auxiliary; not a blueprint node). -/
instance (priority := 10000) supportModules_complexHasTensor (X : Scheme.{u})
    (A B : CochainComplex (supportModules Λ X) ℤ) : HomologicalComplex.HasTensor A B :=
  fun _ ↦ (supportModules_smallColimits Λ X).has_colimits_of_shape _ |>.has_colimit _

/-- The support inverse image is the recorded extension-of-scalars inverse image, via
extension along the invertible coefficient map alpha.
Source: Stacks Tag 09AA (auxiliary; not a blueprint node). -/
noncomputable def supportPullbackIsoUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    supportPullback Λ f ≅ upperStar Λ f :=
  Functor.isoWhiskerLeft ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm

/-- The normalized ordinary tensor comparison exists uniquely as a module isomorphism.
Source: Stacks Tag 03EL (auxiliary; not a blueprint node).
Proof: inverse image preserves the balanced-tensor coequalizer and the abelian-sheaf
tensor. Transport the action along alpha. The displayed equation is the universal
balanced bilinear generator formula, giving existence and uniqueness; the inverse is
obtained from the inverse abelian-sheaf tensor comparison. -/
theorem existsUnique_supportTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : supportModules Λ Y) :
    ∃! e : (supportPullback Λ f).obj (M ⊗ N) ≅
      (supportPullback Λ f).obj M ⊗ (supportPullback Λ f).obj N,
      Functor.LaxMonoidal.μ (ProEtale.upperStar Ab.{u + 1} f) M.X N.X ≫
        (ProEtale.upperStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) ≫ e.hom.hom =
          Mod.tensorObjπ ((supportPullback Λ f).obj M) ((supportPullback Λ f).obj N) := by
  exact existsUnique_mapModComapTensorComparison
    (ProEtale.upperStar Ab.{u + 1} f) (asIso (condensedPullbackHom Λ f)).inv M N

/-- Ordinary pullback-tensor comparison, fixed by its balanced generator formula.
Source: Stacks Tag 03EL (auxiliary; not a blueprint node). -/
noncomputable def supportTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : supportModules Λ Y) :
    (supportPullback Λ f).obj (M ⊗ N) ≅
      (supportPullback Λ f).obj M ⊗ (supportPullback Λ f).obj N :=
  Classical.choose (ExistsUnique.exists (existsUnique_supportTensorComparison Λ f M N))

private noncomputable instance supportPullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (supportPullback Λ f).Monoidal := by
  unfold supportPullback
  infer_instance

private theorem supportTensorComparison_eq_δ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : supportModules Λ Y) :
    (supportTensorComparison Λ f M N).hom =
      Functor.OplaxMonoidal.δ (supportPullback Λ f) M N := by
  let F := ProEtale.upperStar Ab.{u + 1} f
  let ψ := (asIso (condensedPullbackHom Λ f)).inv
  let r := F.mapMod (condensedRingObj Λ Y) ⋙ Mod.comap ψ
  let e := (Functor.Monoidal.μIso r M N).symm
  have he : Mod.tensorObjπ (r.obj M) (r.obj N) ≫ e.inv.hom =
      Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) := by
    change Mod.tensorObjπ (r.obj M) (r.obj N) ≫
      (Mod.comapTensorIso ψ ((F.mapMod _).obj M) ((F.mapMod _).obj N) ≪≫
        (Mod.comap ψ).mapIso (F.mapModTensorIso M N)).hom.hom = _
    dsimp only [r, Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom, Mod.comp_hom']
    rw [← Category.assoc, Mod.tensorπ_comapTensorIso_hom_hom]
    exact F.tensorπ_mapModTensorIso_hom_hom M N
  have hn : Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorObjπ M N) ≫
      e.hom.hom = Mod.tensorObjπ (r.obj M) (r.obj N) := by
    rw [← Category.assoc, ← he, Category.assoc]
    change _ ≫ (e.inv ≫ e.hom).hom = _
    simp only [e.inv_hom_id, Mod.id_hom', Category.comp_id]
  have hchoose := Classical.choose_spec
    (ExistsUnique.exists (existsUnique_supportTensorComparison Λ f M N))
  have hEq := (existsUnique_supportTensorComparison Λ f M N).unique hchoose hn
  exact congrArg Iso.hom hEq

/-- The summand normalization, for an additive functor between monoidal categories.
Source: Stacks Tag 06YL (auxiliary; not a blueprint node). -/
def SupportComplexTensorEquations
    {C : Type w₁} {D : Type w₂} [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (r : C ⥤ D) [r.Additive]
    (t : ∀ M N : C, r.obj (M ⊗ N) ⟶ r.obj M ⊗ r.obj N)
    (A B : CochainComplex C ℤ)
    (d : (r.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj A B) ⟶
      HomologicalComplex.tensorObj ((r.mapHomologicalComplex (.up ℤ)).obj A)
        ((r.mapHomologicalComplex (.up ℤ)).obj B)) : Prop :=
  ∀ (p q n : ℤ) (h : p + q = n),
    r.map (HomologicalComplex.ιTensorObj A B p q n h) ≫ d.f n =
      t (A.X p) (B.X q) ≫
        HomologicalComplex.ιTensorObj ((r.mapHomologicalComplex (.up ℤ)).obj A)
          ((r.mapHomologicalComplex (.up ℤ)).obj B) p q n h

/-- The summand equations specialized to the canonical ordinary pullback comparison.
Source: Stacks Tag 06YL (auxiliary; not a blueprint node). -/
def SupportComplexTensorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (supportModules Λ Y) ℤ)
    (d : ((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.tensorObj A B) ⟶
      HomologicalComplex.tensorObj
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B)) : Prop :=
  SupportComplexTensorEquations (supportPullback Λ f)
    (fun M N ↦ (supportTensorComparison Λ f M N).hom) A B d

/-- The summand comparisons determine a unique chain map.
Source: Stacks Tag 06YL (auxiliary; not a blueprint node).
Proof: inverse image preserves the coproduct over p+q=n. Define the component by the
ordinary tensor comparison on each summand. Naturality with respect to both differentials
and additivity give the chain-map equation with its usual sign. The coproduct universal
property proves uniqueness degree by degree. -/
theorem existsUnique_supportComplexTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (supportModules Λ Y) ℤ) :
    ∃! d : ((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.tensorObj A B) ⟶
      HomologicalComplex.tensorObj
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B),
      SupportComplexTensorNormalization Λ f A B d := by
  let r := supportPullback Λ f
  let : PreservesColimitsOfSize.{0, 0} r :=
    (supportPullbackAdjunction Λ f).leftAdjoint_preservesColimits
  let d := HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans r) (.up ℤ) A B
  have hd : ∀ (p q n : ℤ) (h : p + q = n),
      r.map (HomologicalComplex.ιTensorObj A B p q n h) ≫ d.f n =
        (supportTensorComparison Λ f (A.X p) (B.X q)).hom ≫
          HomologicalComplex.ιTensorObj
            ((r.mapHomologicalComplex (.up ℤ)).obj A)
            ((r.mapHomologicalComplex (.up ℤ)).obj B) p q n h := by
    intro p q n h
    rw [supportTensorComparison_eq_δ]
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      (Functor.OplaxMonoidal.δNatTrans r) (.up ℤ) A B p q n h
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map r
  intro p q h
  exact (hd' p q n h).trans (hd p q n h).symm

/-- The total-complex comparison fixed by its ordinary tensor summands.
Source: Stacks Tag 06YL (auxiliary; not a blueprint node). -/
noncomputable def supportComplexTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (supportModules Λ Y) ℤ) :
    ((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.tensorObj A B) ⟶
      HomologicalComplex.tensorObj
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B) :=
  Classical.choose (ExistsUnique.exists (existsUnique_supportComplexTensorComparison Λ f A B))

/-- The type of candidate derived pullback tensor comparison families.
Source: Stacks Tag 0G7D (auxiliary; not a blueprint node). -/
def SupportDerivedTensorComparisonFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ExactDerivedTensorComparisonFamily (supportPullback Λ f)

/-- Naturality and the localization square on total-complex representatives.
Source: Stacks Tags 06YL and 0G7D
(auxiliary; not a blueprint node).
The tensor maps are those of the existing derivedTensor functors and lax localization. -/
def SupportDerivedTensorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : SupportDerivedTensorComparisonFamily Λ f) : Prop :=
  ExactDerivedTensorNormalization (supportPullback Λ f)
    (supportComplexTensorComparison Λ f) e

private theorem supportPullback_preservesFlat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (supportPullback Λ f).PreservesFlat := by
  exact ProEtale.inverseImageModule_preservesFlat f (condensedRingObj Λ Y)
    (condensedRingObj Λ X) (asIso (condensedPullbackHom Λ f)).inv

private noncomputable instance supportPullbackIsLeftAdjoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (supportPullback Λ f).IsLeftAdjoint :=
  (supportPullbackAdjunction Λ f).isLeftAdjoint

private theorem supportComplexTensorComparison_eq_δ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (supportModules Λ Y) ℤ) :
    supportComplexTensorComparison Λ f A B = HomologicalComplex.mapBifunctorComparison
      (Functor.OplaxMonoidal.δNatTrans (supportPullback Λ f)) (.up ℤ) A B := by
  apply (existsUnique_supportComplexTensorComparison Λ f A B).unique
  · exact Classical.choose_spec
      (ExistsUnique.exists (existsUnique_supportComplexTensorComparison Λ f A B))
  · intro p q n h
    dsimp only
    rw [supportTensorComparison_eq_δ]
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      (Functor.OplaxMonoidal.δNatTrans (supportPullback Λ f)) (.up ℤ) A B p q n h

/-- The normalized derived comparison exists uniquely.
Source: Stacks Tags 03EL, 06YS and 0G7D
(auxiliary; not a blueprint node).
Proof: sum the ordinary comparison over p+q=n. Naturality intertwines the two
differentials, including (-1)^p on the second. Inverse image preserves coproducts,
flat terms and K-flat resolutions. Compute both sides on these resolutions; the
summand maps give an isomorphism. Descend along the two K-flat localization
equivalences. The localization tensor maps give the displayed square on arbitrary
complexes. Its restriction to K-flat pairs, where those maps are invertible, determines
every component uniquely; the factorization isomorphisms extend this to all objects. -/
theorem existsUnique_supportDerivedTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : SupportDerivedTensorComparisonFamily Λ f,
      SupportDerivedTensorNormalization Λ f e := by
  let : (supportPullback Λ f).PreservesFlat := supportPullback_preservesFlat Λ f
  exact existsUnique_exactDerivedTensorComparison (supportPullback Λ f)
    (supportComplexTensorComparison Λ f) (supportComplexTensorComparison_eq_δ Λ f)

/-- Derived pullback-tensor comparison with the specified total-complex normalization.
Source: Stacks Tag 0G7D (auxiliary; not a blueprint node). -/
noncomputable def supportDerivedTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SupportDerivedTensorComparisonFamily Λ f :=
  Classical.choose (ExistsUnique.exists (existsUnique_supportDerivedTensorComparison Λ f))

end AlgebraicGeometry.ProEtale.CondensedRing
