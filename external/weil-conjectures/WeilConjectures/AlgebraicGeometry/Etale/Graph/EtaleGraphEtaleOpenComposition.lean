/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphCoherence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportSumCompositor
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit

/-! # Graph composition with an open second leg

Source: Stacks Project, Tags 0F4L and 0F7J.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

private lemma open_graph_identity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] [QuasiCompact j] :
    canonicalEtaleCompactSupportComparison A j (Compactification.ofIsOpenImmersion j) =
      Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
        (rightDerivedLowerStarIdIso A Z) ≪≫ Functor.rightUnitor _ := by
  let c := Compactification.ofIsOpenImmersion j
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  let R := (lowerStar (ModuleCat.{u + 1} A) (𝟙 Z)).rightDerivedFunctor
  let γ := compactSupportDerivedComparison A j c (etaleCompactificationGraphMap A j c)
  let e : R ≅ 𝟭 _ := rightDerivedLowerStarIdIso A Z
  have := isIso_compactSupportGraphDerivedComparison A j c
  have hh := graph_derived_refinement A j c c (Compactification.Refinement.id c)
  have hc : (Functor.rightDerivedFunctorCompIso'
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 Z))
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 Z))
      (lowerStarComp (ModuleCat.{u + 1} A) (𝟙 Z) (𝟙 Z) (𝟙 Z) (by simp))).hom =
      Functor.whiskerLeft R e.hom := by
    ext M
    rw [← unbounded_pf_comp_inv A (𝟙 Z) (𝟙 Z) (𝟙 Z) (by simp),
      ExchangeFormalism.pfComp'_id_right_inv_app, unbounded_pf_id]
    rfl
  have hm (M : DerivedCategoryModule A X) :
      R.map (γ.app M) ≫ e.hom.app (R.obj (J.obj M)) = 𝟙 _ := by
    have h := congr_app hh M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp] at h
    change γ.app M ≫ R.map (γ.app M) ≫ _ = γ.app M at h
    have h' : γ.app M ≫ R.map (γ.app M) ≫ e.hom.app (R.obj (J.obj M)) =
        γ.app M := by
      simpa only [c, J, R, Compactification.ofIsOpenImmersion,
        refinementOpenCompactification, Compactification.Refinement.id, hc,
        Functor.whiskerLeft_app, Functor.comp_obj, Category.comp_id] using h
    exact (cancel_epi (γ.app M)).1 (h'.trans (Category.comp_id _).symm)
  apply Iso.ext
  ext M
  apply (cancel_epi (γ.app M)).1
  simp only [canonicalEtaleCompactSupportComparison, Iso.symm_hom, asIso_inv,
    NatIso.isIso_inv_app, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  change γ.app M ≫ inv (γ.app M) = γ.app M ≫ e.hom.app (J.obj M) ≫ 𝟙 _
  rw [IsIso.hom_inv_id, Category.comp_id]
  have hn : e.hom.app (J.obj M) ≫ γ.app M =
      R.map (γ.app M) ≫ e.hom.app (R.obj (J.obj M)) :=
    (e.hom.naturality (γ.app M)).symm
  have h := hn.trans (hm M)
  apply (cancel_mono (γ.app M)).1
  calc
    (𝟙 _) ≫ γ.app M = γ.app M := Category.id_comp _
    _ = γ.app M ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = γ.app M ≫ (e.hom.app (J.obj M) ≫ γ.app M) :=
      congrArg (fun t ↦ γ.app M ≫ t) h.symm
    _ = (γ.app M ≫ e.hom.app (J.obj M)) ≫ γ.app M :=
      (Category.assoc _ _ _).symm

private theorem levelwise_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    (K : CochainComplex D ℤ) :
    adj.mapDerivedCategoryAdjunction.counit.app (DerivedCategory.Q.obj K) =
      f.mapDerivedCategory.map (g.mapDerivedCategoryFactors.hom.app K) ≫
        f.mapDerivedCategoryFactors.hom.app ((g.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app K) := by
  have hc := adj.mapDerivedCategoryAdjunction_counit_app_Qh_obj
    ((HomotopyCategory.quotient _ _).obj K)
  have hq {P Q : CochainComplex D ℤ} (k : P ⟶ Q) :
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map k) =
        DerivedCategory.Q.map k := by
    have h := (DerivedCategory.quotientCompQhIso D).hom.naturality k
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at h
    simpa using h
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient, hq] at hc
  change _ = _ ≫ f.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient _ _).obj ((g.mapHomologicalComplex (.up ℤ)).obj K)) ≫ _ at hc
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id] at hc
  have hqc (P : CochainComplex C ℤ) :
      (DerivedCategory.quotientCompQhIso C).hom.app P = 𝟙 _ := rfl
  have hqi (P : CochainComplex D ℤ) :
      (DerivedCategory.quotientCompQhIso D).inv.app P = 𝟙 _ := rfl
  have hqci (P : CochainComplex C ℤ) :
      (DerivedCategory.quotientCompQhIso C).inv.app P = 𝟙 _ := rfl
  simp only [hqc, hqi, hqci, Category.comp_id] at hc
  erw [g.mapDerivedCategory.map_id, f.mapDerivedCategory.map_id] at hc
  simp only [Category.id_comp] at hc
  convert hc using 1 <;> rfl

private theorem levelwise_adjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    : let _ : CatCommSq (f.mapHomologicalComplex (.up ℤ))
        DerivedCategory.Q DerivedCategory.Q f.mapDerivedCategory :=
          ⟨f.mapDerivedCategoryFactors.symm⟩
      let _ : CatCommSq (g.mapHomologicalComplex (.up ℤ))
        DerivedCategory.Q DerivedCategory.Q g.mapDerivedCategory :=
          ⟨g.mapDerivedCategoryFactors.symm⟩
      (adj.mapHomologicalComplex (.up ℤ)).localization
          DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
          DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
          f.mapDerivedCategory g.mapDerivedCategory = adj.mapDerivedCategoryAdjunction := by
  dsimp only
  apply Adjunction.ext_counit
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
  intro K
  rw [levelwise_counit]
  simp only [Adjunction.localization_counit_app, CatCommSq.iso, Iso.symm_inv]

private lemma open_sum_adjunction
    (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j inferInstance =
      derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j := by
  unfold derivedEtaleLowerShriekUpperStarAdjunction
    derivedOpenImmersionLowerShriekUpperStarAdjunction
  rw [levelwise_adjunction]
  rfl

private lemma support_compositor_global
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v]
    (c : Compactification e) (d : Compactification v) (k : Compactification (e ≫ v))
    (M : DerivedCategoryModule A U) :
    (Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso A c (k.ofComp d).restrict) _ ≪≫
      rightDerivedLowerShriekOfCompactificationCompIso A d (k.ofComp d) ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k).hom.app M ≫
        (rightDerivedLowerShriekIso A k).hom.app M =
      (rightDerivedLowerShriekIso A d).hom.app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) v).map
          ((rightDerivedLowerShriekIso A c).hom.app M) ≫
        (unboundedEtaleLowerShriekCompIso A e v).hom.app M := by
  let : HasCompactification e := c.hasCompactification
  let : HasCompactification v := d.hasCompactification
  let : HasCompactification (e ≫ v) := k.hasCompactification
  let r := (k.ofComp d).restrict
  have ht : (rightDerivedLowerShriekOfCompactificationIso A c r).hom =
      (rightDerivedLowerShriekIso A c).hom ≫ (rightDerivedLowerShriekIso A r).inv := by
    apply (cancel_mono (rightDerivedLowerShriekIso A r).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [rightDerivedLowerShriekIso, Iso.trans_hom] using congrArg Iso.hom
      ((unboundedEtaleCompactSupport_comparison_coherence A e).2
        c r (HasCompactification.compactification e))
  have hk := congrArg (fun t ↦ t.hom.app M)
    ((unboundedEtaleCompactSupport_comparison_coherence A (e ≫ v)).2
      (d.comp (k.ofComp d)) k (HasCompactification.compactification (e ≫ v)))
  have hg := NatTrans.congr_app (unboundedEtaleLowerShriekCompIso_tower A e v d
    (k.ofComp d)) M
  simp only [NatTrans.comp_app, NatTrans.hcomp_app] at hg
  rw [hg, ← Category.assoc, ← (rightDerivedLowerShriekIso A d).hom.naturality]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have htM := NatTrans.congr_app ht M
  simp only [NatTrans.comp_app] at htM
  rw [← Functor.map_comp_assoc, ← htM]
  have hk' : (rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k).hom.app
      M ≫ (rightDerivedLowerShriekIso A k).hom.app M =
      (rightDerivedLowerShriekIso A (d.comp (k.ofComp d))).hom.app M := by
    simpa only [rightDerivedLowerShriekIso, Iso.trans_hom, NatTrans.comp_app] using hk
  simpa only [Iso.trans_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Category.assoc] using congrArg
      (fun t ↦ (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((rightDerivedLowerShriekOfCompactificationIso A c r).hom.app M) ≫
          (rightDerivedLowerShriekOfCompactificationCompIso A d (k.ofComp d)).hom.app M ≫ t)
      hk'

/-- The graph comparison identifies etale/open composition with composition of left adjoints.
Source: Stacks Project, Tags 0F4L and 0F7J.
(blueprint: lem-pur-graph-etale-open-composition).

Proof: use the graph refinement equation for the identity refinement of the open
immersion's identity-proper compactification. Cancel its invertible graph map and
use the proper identity composition law and naturality to identify its comparison
with removal of the identity direct image. Localized exact adjunctions agree with
the derived open adjunction by their counits on complexes. The sum composition
counit theorem identifies the sum compositor with the inverse conjugate of
inverse-image composition. Apply the support/sum compositor equation and transport
through the chosen compactification comparisons by naturality and cancellation.
Identity and empty opens and zero coefficients obey the same identities. -/
theorem graph_etale_open_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Z]
    (v : U ⟶ X) [Etale v] [IsSeparated v] [QuasiCompact v]
    (j : X ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    [HasCompactification v] [HasCompactification j] [HasCompactification (v ≫ j)]
    (e : Compactification (v ≫ j)) :
    let s := (conjugateIsoEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (v ≫ j) inferInstance)
      ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance).comp
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j))).symm
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) v j (v ≫ j) rfl) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)
    Functor.isoWhiskerRight (graphChosenEtaleComparison A v)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) j) ≪≫
      Functor.isoWhiskerLeft
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory
        (graphChosenOpenComparison A j) ≪≫ s =
      unboundedEtaleLowerShriekCompIso A v j ≪≫
        (rightDerivedLowerShriekIso A e).symm ≪≫
        canonicalEtaleCompactSupportComparison A (v ≫ j) e := by
  let cv := HasCompactification.compactification v
  let cj := Compactification.ofIsOpenImmersion j
  let β := Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso A cv (e.ofComp cj).restrict) _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A cj (e.ofComp cj) ≪≫
    rightDerivedLowerShriekOfCompactificationIso A (cj.comp (e.ofComp cj)) e
  let σ := derivedEtaleSumCompIso A v j
  have hs : (conjugateIsoEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (v ≫ j) inferInstance)
      ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance).comp
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j))).symm
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) v j (v ≫ j) rfl) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm) = σ := by
    apply (conjugateIsoEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply Iso.ext
    rw [← open_sum_adjunction A j]
    exact (etaleSumCompositionCounit A v j).2.symm
  dsimp only
  rw [hs]
  have hj : graphChosenOpenComparison A j =
      (rightDerivedLowerShriekIso A cj).symm ≪≫
        canonicalEtaleCompactSupportComparison A j cj := by
    unfold graphChosenOpenComparison
    rw [open_graph_identity A j]
    rfl
  rw [hj]
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hg := support_compositor_global A v j cv cj e M
  have hsum := congr_app (etaleSupportSumCompositor A v j cv cj e) M
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc] at hsum
  rw [← (canonicalEtaleCompactSupportComparison A j cj).hom.naturality_assoc] at hsum
  change β.hom.app M ≫ (canonicalEtaleCompactSupportComparison A (v ≫ j) e).hom.app M =
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cj).map
      ((canonicalEtaleCompactSupportComparison A v cv).hom.app M) ≫
      (canonicalEtaleCompactSupportComparison A j cj).hom.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.obj M) ≫
      σ.hom.app M at hsum
  let q := (rightDerivedLowerShriekIso A cj).hom.app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cv).obj M) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) j).map
      ((rightDerivedLowerShriekIso A cv).hom.app M)
  have : IsIso q := by dsimp only [q]; infer_instance
  apply (cancel_epi q).1
  simp only [graphChosenEtaleComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  have hl : q ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) j).map
        ((rightDerivedLowerShriekIso A cv).inv.app M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) j).map
        ((canonicalEtaleCompactSupportComparison A v cv).hom.app M) ≫
      (rightDerivedLowerShriekIso A cj).inv.app _ ≫
      (canonicalEtaleCompactSupportComparison A j cj).hom.app _ ≫ σ.hom.app M =
      β.hom.app M ≫ (canonicalEtaleCompactSupportComparison A (v ≫ j) e).hom.app M := by
    dsimp only [q]
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    rw [← (rightDerivedLowerShriekIso A cj).hom.naturality_assoc]
    simp only [Iso.hom_inv_id_app_assoc]
    exact hsum.symm
  rw [hl]
  dsimp only [q]
  simp only [Category.assoc]
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
    congrArg (fun t ↦ t ≫ (rightDerivedLowerShriekIso A e).inv.app M ≫
      (canonicalEtaleCompactSupportComparison A (v ≫ j) e).hom.app M) hg

end AlgebraicGeometry.Etale
