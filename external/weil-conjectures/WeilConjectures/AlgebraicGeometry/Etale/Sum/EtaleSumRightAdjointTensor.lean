/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointCoherenceSupplement
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizationComparisonCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphTensor
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.CategoryTheory.AdjointProjectionTensorTransfer.AdjointProjectionTensorTransfer
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
import Mathlib.CategoryTheory.Localization.Predicate

/-! # The tensor normalization of the etale sum right adjoint

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality.proof.md, Step 1; Stacks Project Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor).

The comparison is the existing derived graph comparison. The tensor arrow uses the
inverse of the specified compactification projection, transported to exact pullback.
All adjunctions are quantified, and all inputs belong to the ordinary unbounded categories.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso
  unboundedEtaleCompactSupportBaseChange exactEtaleSumExchange

private theorem tensorDerivedCounit
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

private theorem tensorDerivedAdjunction
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
  rw [tensorDerivedCounit]
  simp only [Adjunction.localization_counit_app, CatCommSq.iso, Iso.symm_inv]

private theorem tensorSumAdjunction
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (e : U ⟶ X) [Etale e] :
    derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance =
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
        inferInstance).mapDerivedCategoryAdjunction := by
  unfold derivedEtaleLowerShriekUpperStarAdjunction
  exact tensorDerivedAdjunction
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)

-- Formal counit, unit-transport and naturality calculations for the specified projection mate.
private theorem tensorProjectionCounit
    {C D : Type*} [Category C] [Category D]
    {S : C ⥤ D} {T : D ⥤ C} (adj : S ⊣ T)
    (B : C ⥤ C ⥤ C) (B' : D ⥤ D ⥤ D)
    (δ : (((Functor.whiskeringLeft₂ C).obj T).obj T).obj B ⟶
      (Functor.postcompose₂.obj T).obj B') (X K : D) :
    S.map ((δ.app X).app K) ≫ adj.counit.app ((B'.obj X).obj K) =
      ((adj.projectionMap T B B' δ).app (T.obj X)).app K ≫
        (B'.map (adj.counit.app X)).app K := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  have hp := adj.unit_app_comp_map_projectionMap_app_app T B B' δ (T.obj X) K
  rw [adj.homEquiv_unit, adj.homEquiv_unit]
  change (δ.app X).app K ≫ adj.unit.app (T.obj ((B'.obj X).obj K)) ≫
      T.map (adj.counit.app ((B'.obj X).obj K)) =
    (adj.unit.app ((B.obj (T.obj X)).obj (T.obj K)) ≫
      T.map (((adj.projectionMap T B B' δ).app (T.obj X)).app K)) ≫
        T.map ((B'.map (adj.counit.app X)).app K)
  change adj.unit.app ((B.obj (T.obj X)).obj (T.obj K)) ≫
    T.map (((adj.projectionMap T B B' δ).app (T.obj X)).app K) = _ at hp
  rw [hp]
  change (δ.app X).app K ≫ adj.unit.app _ ≫ T.map (adj.counit.app _) =
    ((B.map (adj.unit.app (T.obj X))).app (T.obj K) ≫
      (δ.app (S.obj (T.obj X))).app K) ≫
        T.map ((B'.map (adj.counit.app X)).app K)
  have hn := NatTrans.congr_app (δ.naturality (adj.counit.app X)) K
  change (B.map (T.map (adj.counit.app X))).app (T.obj K) ≫ (δ.app X).app K =
    (δ.app (S.obj (T.obj X))).app K ≫
      T.map ((B'.map (adj.counit.app X)).app K) at hn
  have ht : (B.map (adj.unit.app (T.obj X))).app (T.obj K) ≫
      (B.map (T.map (adj.counit.app X))).app (T.obj K) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← B.map_comp]
    simp
  rw [Category.assoc, ← hn]
  rw [reassoc_of% ht]
  simp
private theorem tensorUnitTransport
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F G : D ⥤ C} (i : F ≅ G)
    (a : ∀ X Y : D, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (u : F.obj (𝟙_ D) ≅ 𝟙_ C)
    (h : ∀ K : D, (a (𝟙_ D) K).hom ≫
      (u.hom ▷ F.obj K) ≫ (λ_ (F.obj K)).hom = F.map (λ_ K).hom)
    (K : D) :
    (i.inv.app (𝟙_ D) ⊗ₘ i.inv.app K) ≫ (a (𝟙_ D) K).inv ≫
        i.hom.app (𝟙_ D ⊗ K) ≫ G.map (λ_ K).hom =
      ((i.inv.app (𝟙_ D) ≫ u.hom) ▷ G.obj K) ≫ (λ_ (G.obj K)).hom := by
  rw [← i.hom.naturality, ← h K]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [MonoidalCategory.tensorHom_def, comp_whiskerRight, Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality_assoc]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
private theorem tensorDerivedUnitLaw
    (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    [HasSmallSiteSheafify D] {V X : Scheme.{u}} (e : V ⟶ X)
    [(upperStar D e).PreservesFlat]
    [∀ M : D, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]
    [(V.smallEtaleTopology.W (A := D)).IsMonoidal]
    [(X.smallEtaleTopology.W (A := D)).IsMonoidal]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology D) ⥤
      DerivedCategory (Sheaf V.smallEtaleTopology D))
    (i : (upperStar D e).leftDerivedFunctor ≅ E)
    (θ : (((Functor.whiskeringLeft₂ _).obj E).obj E).obj (derivedTensor D V) ≅
      (Functor.postcompose₂.obj E).obj (derivedTensor D X))
    (hθ : θ =
      (((Functor.whiskeringLeft₂ _).mapIso i.symm).app E).app (derivedTensor D V) ≪≫
        (((Functor.whiskeringLeft₂ _).obj
          (upperStar D e).leftDerivedFunctor).mapIso i.symm).app (derivedTensor D V) ≪≫
        (leftDerivedUpperStarTensorNatIso D e).symm ≪≫
        (Functor.postcompose₂.mapIso i).app (derivedTensor D X))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology D)) :
    (θ.hom.app (𝟙_ _)).app K ≫ E.map (derivedTensorLeftUnitor D X K).hom =
      ((derivedTensor D V).map
        (i.inv.app (𝟙_ _) ≫ (leftDerivedUpperStarUnitIso D e).hom)).app (E.obj K) ≫
          (derivedTensorLeftUnitor D V (E.obj K)).hom := by
  rw [hθ]
  simp only [Iso.trans_hom, NatTrans.comp_app, derivedTensor_map_app,
    derivedTensorLeftUnitor, Category.assoc]
  change (i.inv.app (𝟙_ _) ▷ E.obj K) ≫
    ((upperStar D e).leftDerivedFunctor.obj (𝟙_ _) ◁ i.inv.app K) ≫
    (((leftDerivedUpperStarTensorNatIso D e).app (𝟙_ _)).app K).inv ≫
    i.hom.app (𝟙_ _ ⊗ K) ≫ E.map (λ_ K).hom = _
  rw [← MonoidalCategory.tensorHom_def_assoc]
  exact tensorUnitTransport i
    (fun X Y ↦ ((leftDerivedUpperStarTensorNatIso D e).app X).app Y)
    (leftDerivedUpperStarUnitIso D e)
    (leftDerivedUpperStarTensorComparison_leftUnitor_hom D e) K
private theorem tensorCurriedNatural
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {S : C ⥤ D} {T : D ⥤ C}
    (p : S ⋙ curriedTensor D ≅
      (Functor.postcompose₂.obj S).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 C)).obj T).obj (curriedTensor C)))
    {M M' : C} {K K' : D} (f : M ⟶ M') (g : K ⟶ K') :
    (S.map f ⊗ₘ g) ≫ (p.hom.app M').app K' =
      (p.hom.app M).app K ≫ S.map (f ⊗ₘ T.map g) := by
  have hf := NatTrans.congr_app (p.hom.naturality f) K
  have hg := (p.hom.app M').naturality g
  change S.map f ▷ K ≫ (p.hom.app M').app K =
    (p.hom.app M).app K ≫ S.map (f ▷ T.obj K) at hf
  change S.obj M' ◁ g ≫ (p.hom.app M').app K' =
    (p.hom.app M').app K ≫ S.map (M' ◁ T.map g) at hg
  simp only [MonoidalCategory.tensorHom_def, S.map_comp, Category.assoc]
  rw [hg, ← Category.assoc, hf, Category.assoc]

private theorem tensorProjectionNatural
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F S : C ⥤ D} {T : D ⥤ C} (d : F ≅ S)
    (P : ∀ M K, F.obj M ⊗ K ≅ F.obj (M ⊗ T.obj K))
    (p : ∀ M K, S.obj M ⊗ K ≅ S.obj (M ⊗ T.obj K))
    (hp : ∀ M M' K K' (f : M ⟶ M') (g : K ⟶ K'),
      (S.map f ⊗ₘ g) ≫ (p M' K').hom =
        (p M K).hom ≫ S.map (f ⊗ₘ T.map g))
    (hd : ∀ M K, (P M K).hom ≫ d.hom.app (M ⊗ T.obj K) =
      (d.hom.app M ⊗ₘ 𝟙 K) ≫ (p M K).hom)
    (M M' : C) (K K' : D) (f : M ⟶ M') (g : K ⟶ K') :
    (F.map f ⊗ₘ g) ≫ (P M' K').hom =
      (P M K).hom ≫ F.map (f ⊗ₘ T.map g) := by
  apply (cancel_mono (d.hom.app (M' ⊗ T.obj K'))).1
  simp only [Category.assoc]
  rw [hd]
  have hn : (F.map f ⊗ₘ g) ≫ (d.hom.app M' ⊗ₘ 𝟙 K') =
      (d.hom.app M ⊗ₘ 𝟙 K) ≫ (S.map f ⊗ₘ g) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
      d.hom.naturality]
  rw [← Category.assoc, hn, Category.assoc, hp, ← reassoc_of% (hd M K),
    ← d.hom.naturality]
private theorem tensorDerivedTransfer
    (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    {U X : Scheme.{u}}
    {F S : DerivedCategory (Sheaf U.smallEtaleTopology D) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology D)}
    {G T : DerivedCategory (Sheaf X.smallEtaleTopology D) ⥤
      DerivedCategory (Sheaf U.smallEtaleTopology D)}
    (adj : F ⊣ G) (sumAdj : S ⊣ T) (d : F ≅ S)
    (u : T.obj (𝟙_ _) ≅ 𝟙_ _)
    (P : ∀ M K, ((derivedTensor D X).obj (F.obj M)).obj K ≅
      F.obj (((derivedTensor D U).obj M).obj (T.obj K)))
    (p : S ⋙ derivedTensor D X ≅ (Functor.postcompose₂.obj S).obj
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj T).obj (derivedTensor D U)))
    (hd : ∀ M K, (P M K).hom ≫ d.hom.app
      (((derivedTensor D U).obj M).obj (T.obj K)) =
        ((derivedTensor D X).map (d.hom.app M)).app K ≫ (p.hom.app M).app K)
    (hev : ∀ K,
      (p.hom.app (T.obj (𝟙_ _))).app K ≫
          S.map (((derivedTensor D U).map u.hom).app (T.obj K) ≫
            (derivedTensorLeftUnitor D U (T.obj K)).hom) ≫ sumAdj.counit.app K =
        ((derivedTensor D X).map (sumAdj.counit.app (𝟙_ _))).app K ≫
          (derivedTensorLeftUnitor D X K).hom) :
    let rho := conjugateIsoEquiv adj sumAdj d.symm
    let eta := rho.app (𝟙_ _) ≪≫ u
    let tau := fun K ↦ adj.homEquiv _ K
      (F.map (((derivedTensorSymmetry D U).hom.app (T.obj K)).app (G.obj (𝟙_ _))) ≫
        (P (G.obj (𝟙_ _)) K).inv ≫
        ((derivedTensor D X).map (adj.counit.app (𝟙_ _))).app K ≫
        (derivedTensorLeftUnitor D X K).hom)
    (∀ K, tau K ≫ rho.hom.app K =
      ((derivedTensor D U).obj (T.obj K)).map eta.hom ≫
        (derivedTensorRightUnitor D U (T.obj K)).hom) ∧
    (∀ K L (f : K ⟶ L), ((derivedTensor D U).map (T.map f)).app (G.obj (𝟙_ _)) ≫
      tau L = tau K ≫ G.map f) := by
  let := DerivedCategory.symmetricCategory (Sheaf U.smallEtaleTopology D)
  let := DerivedCategory.symmetricCategory (Sheaf X.smallEtaleTopology D)
  have hp := fun M M' K K' f g ↦ tensorCurriedNatural p (M := M) (M' := M')
    (K := K) (K' := K') f g
  have hd' : ∀ M K, (P M K).hom ≫ d.hom.app (M ⊗ T.obj K) =
      (d.hom.app M ⊗ₘ 𝟙 K) ≫ ((p.app M).app K).hom := by
    intro M K
    simpa only [MonoidalCategory.tensorHom_id, derivedTensor_map_app, Iso.app_hom,
      derivedTensor, MonoidalCategory.curriedTensor_obj_obj,
      MonoidalCategory.curriedTensor_map_app] using hd M K
  have hP := tensorProjectionNatural d P (fun M K ↦ (p.app M).app K) hp hd'
  have h := adjointProjectionTensorTransfer adj sumAdj d u P
    (fun M K ↦ (p.app M).app K) hP hp hd' (by
      intro K
      simpa only [MonoidalCategory.tensorHom_id, derivedTensor_map_app,
        derivedTensorLeftUnitor, Iso.app_hom, derivedTensor,
        MonoidalCategory.curriedTensor_obj_obj, MonoidalCategory.curriedTensor_map_app]
        using hev K)
  refine ⟨?_, ?_⟩
  · intro K
    simpa only [AdjointProjectionTensorTransfer.q, AdjointProjectionTensorTransfer.h,
      MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id, Iso.trans_hom, Iso.app_hom,
      derivedTensor_obj_map, derivedTensorRightUnitor, derivedTensorLeftUnitor,
      derivedTensor_map_app, derivedTensorSymmetry, DerivedCategory.canonicalTensorSymmetry,
      BraidedCategory.curriedBraidingNatIso, NatIso.ofComponents_hom_app, derivedTensor,
      conjugateIsoEquiv_apply_hom, Iso.symm_hom,
      MonoidalCategory.curriedTensor_obj_obj, MonoidalCategory.curriedTensor_obj_map,
      MonoidalCategory.curriedTensor_map_app] using h.2.2.2.2.2.2.1 K
  · intro K L f
    simpa only [AdjointProjectionTensorTransfer.q, MonoidalCategory.tensorHom_id,
      derivedTensor_map_app, derivedTensorLeftUnitor, derivedTensorSymmetry,
      DerivedCategory.canonicalTensorSymmetry, BraidedCategory.curriedBraidingNatIso,
      NatIso.ofComponents_hom_app, derivedTensor,
      conjugateIsoEquiv_apply_hom, Iso.symm_hom,
      MonoidalCategory.curriedTensor_obj_obj, MonoidalCategory.curriedTensor_obj_map,
      MonoidalCategory.curriedTensor_map_app]
      using h.2.2.2.2.2.2.2.2.1 K L f

private theorem tensorCounitPreservingComparison
    {C D : Type*} [Category C] [Category D]
    {L S : C ⥤ D} {R T : D ⥤ C}
    (e : L ≅ S) (adj : L ⊣ R) (sumAdj : S ⊣ T) :
    ∃! q : R ≅ T,
      Functor.whiskerLeft R e.hom ≫ Functor.whiskerRight q.hom S ≫ sumAdj.counit =
        adj.counit := by
  let q : R ≅ T := conjugateIsoEquiv adj sumAdj e.symm
  have hq : Functor.whiskerLeft R e.hom ≫
      Functor.whiskerRight q.hom S ≫ sumAdj.counit = adj.counit := by
    ext Y
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    change e.hom.app (R.obj Y) ≫
      S.map (((conjugateEquiv adj sumAdj) e.inv).app Y) ≫ sumAdj.counit.app Y = _
    rw [conjugateEquiv_counit adj sumAdj e.inv Y]
    simp
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Iso.ext
  ext Y
  apply (sumAdj.homEquiv _ _).symm.injective
  change S.map (q'.hom.app Y) ≫ sumAdj.counit.app Y =
    S.map (q.hom.app Y) ≫ sumAdj.counit.app Y
  apply (cancel_epi (e.hom.app (R.obj Y))).1
  exact (NatTrans.congr_app hq' Y).trans (NatTrans.congr_app hq Y).symm

private theorem tensorComparisonVComp
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅]
    {F₀ S₀ : C₀ ⥤ C₁} {F₁ S₁ : C₂ ⥤ C₃} {F₂ S₂ : C₄ ⥤ C₅}
    {H₀ : C₀ ⥤ C₂} {H₁ : C₂ ⥤ C₄} {G₀ : C₁ ⥤ C₃} {G₁ : C₃ ⥤ C₅}
    (a₀ : TwoSquare F₀ H₀ G₀ F₁) (a₁ : TwoSquare F₁ H₁ G₁ F₂)
    (b₀ : TwoSquare S₀ H₀ G₀ S₁) (b₁ : TwoSquare S₁ H₁ G₁ S₂)
    (e₀ : F₀ ≅ S₀) (e₁ : F₁ ≅ S₁) (e₂ : F₂ ≅ S₂)
    (h₀ : a₀ ≫ Functor.whiskerLeft H₀ e₁.hom =
      Functor.whiskerRight e₀.hom G₀ ≫ b₀)
    (h₁ : a₁ ≫ Functor.whiskerLeft H₁ e₂.hom =
      Functor.whiskerRight e₁.hom G₁ ≫ b₁) :
    (a₀.vComp a₁) ≫ Functor.whiskerLeft (H₀ ⋙ H₁) e₂.hom =
      Functor.whiskerRight e₀.hom (G₀ ⋙ G₁) ≫ (b₀.vComp b₁) := by
  ext K
  have h₀K := NatTrans.congr_app h₀ K
  have h₁K := NatTrans.congr_app h₁ (H₀.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h₀K h₁K
  simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Category.id_comp, Category.comp_id, Category.assoc]
  rw [h₁K, ← G₁.map_comp_assoc, h₀K, G₁.map_comp, Category.assoc]

-- Retain the actual graph comparison as data; its coherence supplies only proof fields.
private noncomputable def tensorCanonicalNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    EtaleCompactSupportNormalization A := by
  let core := canonicalEtaleCompactSupportCore A
  have coh := etaleCompactSupportGraph_coherence A
  exact {
    comparison := core.comparison
    sheafComparison := core.sheafComparison
    sheaf_normalization := core.sheaf_normalization
    derived_normalization := core.derived_normalization
    base_change := coh.base_change
    composition := by
      intro U X X' X'' f hf hs hq hU hUc hX hXc hX' hX'c hX'' hX''c c g k
      exact tensorComparisonVComp
        (exactCompactSupportExchangeSquare A c g)
        (exactCompactSupportExchangeSquare A
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip) k)
        (exactEtaleSumExchangeSquare A f g)
        (exactEtaleSumExchangeSquare A (pullback.fst g f) k)
        (core.comparison f c)
        (core.comparison (pullback.fst g f)
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip))
        (core.comparison (pullback.fst k (pullback.fst g f))
          ((c.ofIsPullback (IsPullback.of_hasPullback g f).flip).ofIsPullback
            (IsPullback.of_hasPullback k (pullback.fst g f)).flip))
        (coh.base_change f c g)
        (coh.base_change (pullback.fst g f)
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip) k)
    refinement := coh.refinement
    identity := coh.identity
    adjunction := by
      intro U X f hf hs hU hUc hX hXc c R adj
      exact tensorCounitPreservingComparison (core.comparison f c) adj
        (Adjunction.mapDerivedCategoryAdjunction
          (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f inferInstance))
  }

private theorem projection_transpose
    {C D : Type*} [Category C] [Category D]
    {P : C ⥤ D} {R : D ⥤ C} (adj : P ⊣ R)
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (δ : (Functor.postcompose₂.obj P).obj T ⟶
      (((Functor.whiskeringLeft₂ _).obj P).obj P).obj T')
    {A B K : C} {J J' : D}
    (q : A ⟶ (T.obj B).obj K) (t : B ⟶ R.obj J)
    (γ : (T'.obj J).obj (P.obj K) ⟶ J') :
    (adj.homEquiv _ _).symm
      (q ≫ (T.map t).app K ≫
        ((adj.rightAdjointProjectionMap δ).app J).app K ≫ R.map γ) =
      P.map q ≫ (δ.app B).app K ≫
        (T'.map ((adj.homEquiv _ _).symm t)).app (P.obj K) ≫ γ := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hγ := adj.counit.naturality γ
  simp only [Functor.comp_map, Functor.id_map] at hγ
  rw [hγ]
  have hπ := adj.map_rightAdjointProjectionMap_app_app_comp_counit δ J K
  change P.map (((adj.rightAdjointProjectionMap δ).app J).app K) ≫
    adj.counit.app ((T'.obj J).obj (P.obj K)) =
      (δ.app (R.obj J)).app K ≫ (T'.map (adj.counit.app J)).app (P.obj K) at hπ
  rw [reassoc_of% hπ]
  have hn := NatTrans.congr_app (δ.naturality t) K
  change P.map ((T.map t).app K) ≫ (δ.app (R.obj J)).app K =
    (δ.app B).app K ≫ (T'.map (P.map t)).app (P.obj K) at hn
  rw [reassoc_of% hn]
  simp only [NatTrans.comp_app, Category.assoc]

-- The graph-evaluation transpose argument works for this fixed normalization as well.
private theorem tensorProjectionCompatibility
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    (M : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).map
            ((leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) e).hom.app K)) ≫
        (N.comparison e c).hom.app (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ≫
        ((etaleSupportSumProjectionReverse A e).app M).app K =
      ((derivedTensor (ModuleCat.{u + 1} A) T).map
        ((N.comparison e c).hom.app M)).app K := by
  let O := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let R := (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor
  let E := (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
  let S := (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
  let T₀ := derivedTensor (ModuleCat.{u + 1} A) T
  let V₀ := derivedTensor (ModuleCat.{u + 1} A) V
  let t := (N.comparison e c).inv
  let q := ((etaleSupportSumProjectionReverse A e).app M).app K
  let γ := ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) c.i).inv.app M).app
      ((upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K) ≫
    O.map ((V₀.obj M).map
      ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app K)) ≫
    O.map ((V₀.obj M).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K))
  let sumAdj := (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
    inferInstance).mapDerivedCategoryAdjunction
  have hq : sumAdj.unit.app _ ≫ E.map q =
      (V₀.map (sumAdj.unit.app M)).app (E.obj K) ≫
        (etaleSumExtensionTensorPullbackIso A e (S.obj M) K).hom := by
    exact sumAdj.unit_app_comp_map_projectionMap_app_app E V₀ T₀
      (etaleSupportExactUpperTensorIso A e).hom M K
  have hgraph := compactSupportGraph_tensor_evaluation A N e c M K q hq
  change (upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.map q ≫
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) c.g).app (S.obj M)).app K ≫
      ((derivedTensor (ModuleCat.{u + 1} A) c.Z).map
        (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g).homEquiv _ _).symm
          (t.app M))).app ((upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K) ≫ γ =
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g).homEquiv _ _).symm
      (t.app ((V₀.obj M).obj (E.obj K))) at hgraph
  have hc : q ≫ (T₀.map (t.app M)).app K ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((V₀.obj M).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K)) =
      t.app ((V₀.obj M).obj (E.obj K)) := by
    apply ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) c.g).homEquiv _ _).symm.injective
    have ht := projection_transpose
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
      T₀ (derivedTensor (ModuleCat.{u + 1} A) c.Z)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) c.g) q (t.app M) γ
    apply Eq.trans _ hgraph
    convert ht using 1
    simp only [projectionMapOfCompactification_app_app, Functor.comp_map,
      Functor.map_comp, Category.assoc, γ]
    rfl
  obtain ⟨a, n, p, hp⟩ := etaleSupportMapCompatibility A
  have : IsIso (etaleSupportSumProjectionReverse A e) := by
    rw [← hp.2.1 e]
    infer_instance
  apply (cancel_epi (q ≫ (T₀.map (t.app M)).app K)).1
  simp only [Category.assoc]
  erw [reassoc_of% hc]
  dsimp only [t]
  rw [Iso.inv_hom_id_app_assoc]
  have ht : (T₀.map ((N.comparison e c).inv.app M)).app K ≫
      (T₀.map ((N.comparison e c).hom.app M)).app K = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← T₀.map_comp, Iso.inv_hom_id_app,
      T₀.map_id, NatTrans.id_app]
  change q = q ≫ _
  rw [ht]
  exact (Category.comp_id q).symm

/-- The conjugate of the inverse canonical graph comparison for a fixed compactification.
Source: blueprint Step 1; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorRho
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    G ≅ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory :=
  conjugateIsoEquiv adj
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
    (canonicalEtaleCompactSupportComparison A e c).symm

attribute [local irreducible] etaleTensorRho

/-- The coefficient normalization eta is rho at the unit followed by coefficient pullback.
Source: blueprint Step 1; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorEta
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    G.obj (constantComplex A X) ≅ constantComplex A U :=
  (etaleTensorRho A e c G adj).app (constantComplex A X) ≪≫ etaleSumPullbackUnitIso A e

attribute [local irreducible] etaleTensorEta

/-- The specified compactification projection, with exact rather than left-derived pullback.
Source: Stacks Tag 0GKF, support-map compatibility (2)
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorProjection
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (e : U ⟶ X)
    (c : Compactification e) (M : DerivedCategoryModule A U) (K : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj K ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K))

attribute [local irreducible] etaleTensorProjection

/-- The specified projection is invertible, including compactifications with nonfinite proper part.
Source: Stacks Tag 0GKF; blueprint Step 1
(blueprint: lem-pur-etale-sum-right-adjoint-tensor).

Proof: Support-map compatibility (2) conjugates this arrow by the canonical graph comparison
to the derived sum projection. The latter is an isomorphism: on sheaves its generator rule
is distribution over lift-indexed sums, and flat K-flat resolutions and sum totalization
descend that rule to arbitrary unbounded inputs. Cancel the graph comparison isomorphisms. -/
theorem isIso_etaleTensorProjection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (M : DerivedCategoryModule A U) (K : DerivedCategoryModule A X) :
    IsIso (etaleTensorProjection A e c M K) := by
  classical
  obtain ⟨a, n, p, hp⟩ := etaleSupportMapCompatibility A
  have h := hp.2.2.2.1 e c M K
  have : IsIso ((n e c).hom.app
      (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K))) := by
    dsimp
    infer_instance
  have : IsIso (((derivedTensor (ModuleCat.{u + 1} A) X).map
      ((n e c).hom.app M)).app K) := by infer_instance
  have : IsIso (((p e).hom.app M).app K) := by infer_instance
  have : IsIso (etaleTensorProjection A e c M K ≫ (n e c).hom.app
      (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K))) := by
    rw [show etaleTensorProjection A e c M K ≫ (n e c).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) = _ by
      simpa only [etaleTensorProjection, Category.assoc] using h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((n e c).hom.app
    (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)))

/-- The displayed inverse transpose defining tau, as an actual compact-support morphism.
Source: blueprint Step 1, displayed inverse-transpose formula; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorInverseTranspose
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (((derivedTensor (ModuleCat.{u + 1} A) U).obj
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).obj
          (G.obj (constantComplex A X))) ⟶ K :=
  haveI := isIso_etaleTensorProjection A e c (G.obj (constantComplex A X)) K
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) U).hom.app
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).app
          (G.obj (constantComplex A X))) ≫
    inv (etaleTensorProjection A e c (G.obj (constantComplex A X)) K) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
      (adj.counit.app (constantComplex A X))).app K ≫
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X K).hom

attribute [local irreducible] etaleTensorInverseTranspose

/-- The tensor transpose tau under the chosen compact-support adjunction.
Source: blueprint Step 1, displayed inverse-transpose formula; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorTau
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (K : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) U).obj
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).obj
        (G.obj (constantComplex A X)) ⟶ G.obj K :=
  adj.homEquiv _ _ (etaleTensorInverseTranspose A e c G adj K)

attribute [local irreducible] etaleTensorTau

/-- Counit characterization and the tensor equality, as maps natural in every unbounded K.
Source: blueprint Step 1; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor).

Proof:
1. Conjugate the inverse graph comparison. The defining mate equation, composed with d,
   gives ev S(rho) d = epsilon. Conversely the sum-adjunction Hom bijection makes rho
   the unique natural transformation satisfying this equation. For a : F N -> K, naturality
   gives J_S(a d_N^{-1}) = J_F(a) rho_K.
2. At the sheaf level the sum projection sends (s,b) tensor h to (s,b tensor s^*h).
   Evaluation followed by coefficient multiplication sends both sides of the unit-counit
   identity to b h. Linearity, tensor universality and sheafification give equality of maps;
   inverse image is restriction on etale test objects and respects the constant-ring action.
3. Choose flat-term K-flat representatives. Pullback and sum extension preserve these;
   sum totalization identifies the projection with the same generator map in every degree.
   The termwise sum/restriction adjunction descends its evaluation counit. The coefficient
   unit has degree zero, so the differentials agree. Tensor descent and localization give
   the unit-counit identity naturally on all unbounded K.
4. Apply support-map compatibility (2) to replace the inverse specified projection in the
   inverse transpose q_F of tau. Naturality of d gives q_F d^{-1} as the sum inverse
   projection followed by (epsilon at the unit) tensor 1 and the left unitor.
5. Substitute epsilon d^{-1} = ev S(rho) at the unit. Naturality of sum projection moves
   rho through it. The identity of step 3 reduces the result to ev S of
   lambda ((eta tensor 1) sym). Signed symmetry and its unit constraint identify this arrow
   with the right unitor after 1 tensor eta; no Koszul sign is omitted.
6. Transpose under the sum adjunction, using step 1. This gives tau rho = (1 tensor eta)
   unitor. Every construction is natural in K, giving the final naturality clause.
-/
theorem etaleSumRightAdjointTensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    (∀ r : G ⟶ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory,
      (∀ K : DerivedCategoryModule A X,
        (canonicalEtaleCompactSupportComparison A e c).hom.app (G.obj K) ≫
          (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
            (r.app K) ≫
          (derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app K = adj.counit.app K) ↔
        r = (etaleTensorRho A e c G adj).hom) ∧
    (∀ K : DerivedCategoryModule A X,
      etaleTensorTau A e c G adj K ≫ (etaleTensorRho A e c G adj).hom.app K =
        ((derivedTensor (ModuleCat.{u + 1} A) U).obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).map
            (etaleTensorEta A e c G adj).hom ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) U
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).hom) ∧
    (∀ (K L : DerivedCategoryModule A X) (f : K ⟶ L),
      ((derivedTensor (ModuleCat.{u + 1} A) U).map
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map f)).app
          (G.obj (constantComplex A X)) ≫ etaleTensorTau A e c G adj L =
        etaleTensorTau A e c G adj K ≫ G.map f) := by
  classical
  let S := (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
  let T := (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
  let B := derivedTensor (ModuleCat.{u + 1} A) U
  let B' := derivedTensor (ModuleCat.{u + 1} A) X
  let sa := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance
  let d := canonicalEtaleCompactSupportComparison A e c
  let u₀ := etaleSumPullbackUnitIso A e
  obtain ⟨a, n, p, hp⟩ := etaleSupportMapCompatibility A
  have hi : (p e).inv = etaleSupportSumProjectionReverse A e := hp.2.1 e
  have hPi : ∀ M K, IsIso (etaleTensorProjection A e c M K) :=
    isIso_etaleTensorProjection A e c
  let P := fun M K ↦ asIso (etaleTensorProjection A e c M K)
  have hd : ∀ M K, (P M K).hom ≫ d.hom.app ((B.obj M).obj (T.obj K)) =
      (B'.map (d.hom.app M)).app K ≫ ((p e).hom.app M).app K := by
    intro M K
    have hc := tensorProjectionCompatibility A (tensorCanonicalNormalization A) e c M K
    simp only [tensorCanonicalNormalization, canonicalEtaleCompactSupportCore] at hc
    change ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((B.obj M).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K)) ≫
        d.hom.app ((B.obj M).obj (T.obj K)) ≫
          ((etaleSupportSumProjectionReverse A e).app M).app K =
      (B'.map (d.hom.app M)).app K at hc
    have hh := NatTrans.congr_app (NatTrans.congr_app hi M) K
    rw [← hh] at hc
    dsimp only [P, asIso_hom]
    rw [etaleTensorProjection]
    apply (cancel_mono (((p e).inv.app M).app K)).1
    simp only [Category.assoc, Iso.hom_inv_id_app_app]
    exact hc.trans (Category.comp_id _).symm
  have hu := tensorDerivedUnitLaw (ModuleCat.{u + 1} A) e T
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e)
    (etaleSupportExactUpperTensorIso A e) rfl
  have hev : ∀ K,
      ((p e).hom.app (T.obj (constantComplex A X))).app K ≫
          S.map ((B.map u₀.hom).app (T.obj K) ≫
            (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) U (T.obj K)).hom) ≫
          sa.counit.app K =
        (B'.map (sa.counit.app (constantComplex A X))).app K ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X K).hom := by
    intro K
    have hθ := tensorProjectionCounit sa B B'
      (etaleSupportExactUpperTensorIso A e).hom (constantComplex A X) K
    have hn := sa.counit.naturality
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X K).hom
    change S.map (T.map _) ≫ sa.counit.app K = sa.counit.app _ ≫ _ at hn
    have hh := NatTrans.congr_app (NatTrans.congr_app hi
      (T.obj (constantComplex A X))) K
    unfold etaleSupportSumProjectionReverse at hh
    dsimp only [sa] at hθ
    rw [tensorSumAdjunction A e, ← hh] at hθ
    have hunit := hu K
    change ((etaleSupportExactUpperTensorIso A e).hom.app (constantComplex A X)).app K ≫
      T.map (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X K).hom =
        (B.map u₀.hom).app (T.obj K) ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) U (T.obj K)).hom at hunit
    rw [← hunit, S.map_comp, Category.assoc, hn]
    have hθ' := hθ
    rw [← tensorSumAdjunction A e] at hθ'
    change ((p e).hom.app (T.obj (constantComplex A X))).app K ≫
      S.map (((etaleSupportExactUpperTensorIso A e).hom.app
        (constantComplex A X)).app K) ≫
      sa.counit.app ((B'.obj (constantComplex A X)).obj K) ≫
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X K).hom = _
    change S.map _ ≫ sa.counit.app _ = _ at hθ'
    rw [reassoc_of% hθ']
    rw [← Category.assoc, ← Category.assoc]
    erw [Iso.hom_inv_id_app_app, Category.id_comp]
  have h := tensorDerivedTransfer (ModuleCat.{u + 1} A) adj sa d u₀ P (p e) hd hev
  refine ⟨?_, ?_, ?_⟩
  · intro r
    have hc (K) : d.hom.app (G.obj K) ≫
        S.map ((etaleTensorRho A e c G adj).hom.app K) ≫ sa.counit.app K =
          adj.counit.app K := by
      simp only [etaleTensorRho, conjugateIsoEquiv_apply_hom, Iso.symm_hom]
      change d.hom.app (G.obj K) ≫
        S.map ((conjugateEquiv adj sa d.inv).app K) ≫ sa.counit.app K = _
      rw [conjugateEquiv_counit]
      simp
    constructor
    · intro hr
      ext K
      apply (sa.homEquiv _ _).symm.injective
      change S.map (r.app K) ≫ sa.counit.app K =
        S.map ((etaleTensorRho A e c G adj).hom.app K) ≫ sa.counit.app K
      apply (cancel_epi (d.hom.app (G.obj K))).1
      exact (hr K).trans (hc K).symm
    · rintro rfl
      exact hc
  · simpa only [etaleTensorTau, etaleTensorInverseTranspose, etaleTensorRho,
      etaleTensorEta, P, constantComplex, asIso_inv] using h.1
  · simpa only [etaleTensorTau, etaleTensorInverseTranspose, P, constantComplex,
      asIso_inv] using h.2

end AlgebraicGeometry.Etale
