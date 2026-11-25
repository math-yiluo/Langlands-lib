/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square

import WeilConjectures.AlgebraicGeometry.Derived.DerivedExchangeModuleTermwiseSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Unbounded proper/open AdjunctionNormalization

Source: Stacks Project, Tags 0F7B.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma comparison_naturality
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ E) [F.Additive]
    {J I : CochainComplex C ℤ} [J.IsKInjective] [I.IsKInjective] (f : J ⟶ I) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (F.rightDerivedFunctorObjQIso I).hom =
      (F.rightDerivedFunctorObjQIso J).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  have h₁ := (DerivedCategory.quotientCompQhIso C).inv.naturality f
  have h₂ := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ _).map f)
  have h₃ := (DerivedCategory.quotientCompQhIso E).hom.naturality
    ((F.mapHomologicalComplex _).map f)
  dsimp at h₁ h₂ h₃
  dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  rw [← F.rightDerivedFunctor.map_comp_assoc, h₁, F.rightDerivedFunctor.map_comp,
    Category.assoc, Category.assoc, cancel_epi, Category.assoc,
    IsIso.eq_inv_comp, ← reassoc_of% h₂]
  simp only [IsIso.hom_inv_id_assoc]
  exact h₃

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma exact_unit_Q
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions E]
    {F : C ⥤ E} {G : E ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (K : CochainComplex C ℤ) :
    adj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  have h := adj.mapDerivedCategoryAdjunction_unit_app_fac
    ((HomotopyCategory.quotient C (.up ℤ)).obj K)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  have hG := G.mapDerivedCategoryFactorsh_hom_app
    ((F.mapHomologicalComplex (.up ℤ)).obj K)
  erw [F.mapDerivedCategoryFactorsh_hom_app, hG] at h
  simp only [Functor.mapHomotopyCategoryFactors, CategoryTheory.Quotient.lift.isLift_inv] at h
  dsimp only [Functor.comp_obj] at h
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h
  change adj.mapDerivedCategoryAdjunction.unit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≫
      G.mapDerivedCategory.map
        (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app K) ≫
          F.mapDerivedCategoryFactors.hom.app K ≫
          (DerivedCategory.quotientCompQhIso E).inv.app _) ≫
      (G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso E).hom.app _) ≫
        G.mapDerivedCategoryFactors.hom.app _ ≫
        (DerivedCategory.quotientCompQhIso C).inv.app _) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app K)) at h
  simp only [Functor.map_comp, Category.assoc] at h
  have hu := adj.mapDerivedCategoryAdjunction.unit.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app K)
  simp only [Functor.id_map, Functor.comp_map] at hu
  have hh := congrArg (fun t ↦ t ≫ (DerivedCategory.quotientCompQhIso C).hom.app
    ((G.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K))) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  rw [← reassoc_of% hu] at hh
  erw [DerivedCategory.quotientCompQhIso_hom_naturality] at hh
  have hc := G.mapDerivedCategory.map_comp
    ((DerivedCategory.quotientCompQhIso E).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K))
    ((DerivedCategory.quotientCompQhIso E).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K))
  simp only [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id] at hc
  rw [reassoc_of% hc.symm] at hh
  simp only [Functor.id_obj] at hh
  erw [Category.comp_id] at hh
  exact (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app K)).mp hh

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma open_transpose_Q
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j]
    (X : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (Y : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (m : (((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj X ⟶ Y) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
        (DerivedCategory.Q.obj X) ≫
      D((j)^*[ModuleCat.{u + 1} A]).map
        (((j)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app X ≫
          DerivedCategory.Q.map m) ≫
      ((j)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app Y =
    DerivedCategory.Q.map
      (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).mapHomologicalComplex
         (.up ℤ)).unit.app X ≫
        (((j)^*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map m) := by
  rw [Functor.map_comp, Category.assoc]
  have hn := ((j)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.naturality m
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  erw [reassoc_of% (exact_unit_Q
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j) X),
    DerivedCategory.Q.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma support_exchange
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] (sq : CommSq k r p i)
    (θ : (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
      (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hθ : θ.hom.app F ≫
        (p)_*[ModuleCat.{u + 1} A].map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
          ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
        ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
      (i)^*[ModuleCat.{u + 1} A].map (θ.hom.app F) ≫
      (baseChangeMap (ModuleCat.{u + 1} A) sq).app
        ((k)_!open[ModuleCat.{u + 1} A].obj F) =
    (r)_*[ModuleCat.{u + 1} A].map
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k).unit.app F) := by
  have hs : θ.hom.app F ≫ (p)_*[ModuleCat.{u + 1} A].map
      ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
      (squareLowerStarIso (ModuleCat.{u + 1} A) sq).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
        ((r)_*[ModuleCat.{u + 1} A].obj F) := by
    dsimp only [squareLowerStarIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
    change θ.hom.app F ≫ _ ≫ _ ≫ _ = _
    have h := congrArg (fun t ↦ t ≫
      (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).inv.app F) hθ
    simp only [Category.assoc, Iso.hom_inv_id_app] at h
    exact h.trans (Category.comp_id _)
  have hm := mateEquiv_counit_symm (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) k)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
    (TwoSquare.mk _ _ _ _ (squareLowerStarIso (ModuleCat.{u + 1} A) sq).hom) F
  rw [← baseChangeSquare_eq_mateEquiv_symm] at hm
  change (i)^*[ModuleCat.{u + 1} A].map
      ((squareLowerStarIso (ModuleCat.{u + 1} A) sq).hom.app F) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app _ =
    (baseChangeMap (ModuleCat.{u + 1} A) sq).app ((k)_*[ModuleCat.{u + 1} A].obj F) ≫
      (r)_*[ModuleCat.{u + 1} A].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) k).counit.app F) at hm
  have he := congrArg (fun t ↦
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
        ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
      (i)^*[ModuleCat.{u + 1} A].map t ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app _) hs
  simp only [Functor.map_comp, Category.assoc] at he
  rw [hm] at he
  rw [reassoc_of% (baseChangeMap_naturality (ModuleCat.{u + 1} A) sq
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F)),
    ← Functor.map_comp] at he
  rw [unit_map_openImmersionLowerShriekToLowerStar_app_counit] at he
  let t := (k)^*[ModuleCat.{u + 1} A].map
      ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) k).counit.app F
  have ht : (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) k).unit.app F ≫ t = 𝟙 F :=
    unit_map_openImmersionLowerShriekToLowerStar_app_counit (ModuleCat.{u + 1} A) k F
  have ht' : t = inv ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) k).unit.app F) :=
    IsIso.inv_eq_of_hom_inv_id ht |>.symm
  have : IsIso t := by rw [ht']; infer_instance
  apply (cancel_mono ((r)_*[ModuleCat.{u + 1} A].map t)).mp
  rw [Category.assoc, ← Functor.map_comp, ht]
  erw [CategoryTheory.Functor.map_id]
  exact he

private instance restriction_preserves_kinjective
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (k : U ⟶ V) [IsOpenImmersion k] :
    ((k)^*[ModuleCat.{u + 1} A]).PreservesKInjectiveComplexes :=
  (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
    |>.preservesKInjectiveComplexes

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma exchange_on_injective
    (A : Type (u + 1)) [CommRing A] {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (sq : IsPullback k r p i)
    (I : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective] :
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
        (DerivedCategory.Q.obj I) ≫
      R((r)_*[ModuleCat.{u + 1} A]).map
        (((k)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app I) ≫
      (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso
        ((((k)^*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I)).hom =
    D((i)^*[ModuleCat.{u + 1} A]).map
        ((((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom) ≫
      ((i)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
        ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq) (.up ℤ)).app I) := by
  have := (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) k).preservesKInjectiveComplexes
  let c : ChosenCartesianSquare k r p i :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have h := derivedExchangeModuleTermwise A c (DerivedCategory.Q.obj I) I (Iso.refl _)
    ((((k)^*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I) (𝟙 _)
  dsimp only [moduleExchangeDirectImageIso, moduleExchangeReplacementIso,
    moduleExchangeRepresentativeMap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.refl_inv, Iso.trans_inv, Functor.mapIso_inv, asIso_inv, Iso.app_inv] at h
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h
  apply (cancel_epi
    (((i)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.inv.app
        ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I) ≫
      D((i)^*[ModuleCat.{u + 1} A]).map
        ((((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).inv))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc] at h
  rw [reassoc_of% h]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [IsIso.inv_id, Category.comp_id, Category.comp_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private lemma iso_of_normalization
    {C E B T : Type*} [Category C] [Category E] [Category B] [Category T]
    {F : C ⥤ E} {G : E ⥤ C} (a : F ⊣ G) [IsIso a.unit]
    {H : B ⥤ T} {L : T ⥤ B} (b : H ⊣ L) [IsIso b.unit]
    (P : E ⥤ T) (R : C ⥤ B) (gamma : R ⋙ H ≅ F ⋙ P)
    (ex : P ⋙ L ⟶ G ⋙ R)
    (hc : ∀ X, b.unit.app (R.obj X) ≫ L.map (gamma.hom.app X) ≫
      ex.app (F.obj X) = R.map (a.unit.app X)) :
    ∃ lam : F ⋙ P ⋙ L ≅ R,
      (∀ X, lam.hom.app X = ex.app (F.obj X) ≫ R.map (inv (a.unit.app X))) ∧
      ∀ X, gamma.hom.app X = H.map (lam.inv.app X) ≫ b.counit.app (P.obj (F.obj X)) := by
  let e : R ≅ F ⋙ P ⋙ L :=
    (R.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft R (asIso b.unit)) ≪≫
      (Functor.associator R H L).symm ≪≫ Functor.isoWhiskerRight gamma L ≪≫
      Functor.associator F P L
  have he (X : C) : e.hom.app X = b.unit.app (R.obj X) ≫
      L.map (gamma.hom.app X) := by
    simp [e]
  refine ⟨e.symm, ?_, ?_⟩
  · intro X
    apply (cancel_epi (e.hom.app X)).mp
    rw [Iso.symm_hom, Iso.hom_inv_id_app, he, Category.assoc, reassoc_of% hc X,
      ← R.map_comp, IsIso.hom_inv_id, R.map_id]
  · intro X
    change gamma.hom.app X = H.map (e.hom.app X) ≫ _
    rw [he]
    change gamma.hom.app X = (b.homEquiv _ _).symm (b.homEquiv _ _ (gamma.hom.app X))
    exact ((b.homEquiv _ _).symm_apply_apply (gamma.hom.app X)).symm

/-- Adjunction normalization of comparisons normalized on K-injective representatives.
Source: Stacks Project, Tags 0F7B.
(blueprint: lem-amb-unbounded-proper-open-adjunction-normalization).

Proof:
For a cartesian square, apply the sheaf support normalization and restrict along i.
Under the open-unit identifications the ordinary exchange sends i*theta followed by the
open unit to r* of the other open unit. Resolve k!J by a K-injective I. Exact restriction
preserves the resolution, and k*I is K-injective because restriction is right adjoint to
exact extension by zero. The exchange representative formula and naturality along the
resolution show that the displayed lambda, followed by the adjunct of Gamma, is identity.
The representative normalization makes Gamma an isomorphism. The open unit is also an
isomorphism, so the adjunct is invertible. Its inverse is lambda. Descend the resulting
natural isomorphism and apply the inverse adjunction formula to get the asserted counit
expression. This works for unbounded J because no truncation occurs.
-/
theorem unboundedProperOpenAdjunctionNormalization_of_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (θ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (Γ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]))
    (hθ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F))
    (hΓ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective]
        (ρ : ((k)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        D((i)_!open[ModuleCat.{u + 1} A]).map
            (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).hom ≫
          ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
            (((r)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (θ k r p i sq).hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            (((p)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ) =
        (Γ k r p i sq).hom.app (DerivedCategory.Q.obj J) ≫
          R((p)_*[ModuleCat.{u + 1} A]).map
            (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom)) :
    (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : IsPullback k r p i),
        ∃ lam : D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) ⋙
            D((i)^*[ModuleCat.{u + 1} A]) ≅ R((r)_*[ModuleCat.{u + 1} A]),
          (∀ K : DerivedCategoryModule A U,
            lam.hom.app K =
              (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
                  (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
                R((r)_*[ModuleCat.{u + 1} A]).map
                  (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction
                    (ModuleCat.{u + 1} A) k).unit.app K))) ∧
          ∀ K : DerivedCategoryModule A U,
            (Γ k r p i sq.toCommSq).hom.app K =
              D((i)_!open[ModuleCat.{u + 1} A]).map (lam.inv.app K) ≫
                (derivedOpenImmersionLowerShriekUpperStarAdjunction
                  (ModuleCat.{u + 1} A) i).counit.app
                    (R((p)_*[ModuleCat.{u + 1} A]).obj
                      (D((k)_!open[ModuleCat.{u + 1} A]).obj K))) := by
  intro U V W Z _ _ _ _ k r p i _ _ _ _ sq
  let adjk := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k
  let adji := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i
  have : IsIso adji.unit :=
    isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit (ModuleCat.{u + 1} A) i
  have : IsIso adjk.unit :=
    isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit (ModuleCat.{u + 1} A) k
  let gamma := Γ k r p i sq.toCommSq
  let alpha : R((r)_*[ModuleCat.{u + 1} A]) ⟶
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) ⋙
        D((i)^*[ModuleCat.{u + 1} A]) :=
    Functor.whiskerLeft R((r)_*[ModuleCat.{u + 1} A]) adji.unit ≫
      Functor.whiskerRight gamma.hom D((i)^*[ModuleCat.{u + 1} A])
  have halpha (K : DerivedCategoryModule A U) : alpha.app K =
      adji.unit.app (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
        D((i)^*[ModuleCat.{u + 1} A]).map (gamma.hom.app K) := rfl
  have hJ (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      [J.IsKInjective] :
      alpha.app (DerivedCategory.Q.obj J) ≫
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
          (D((k)_!open[ModuleCat.{u + 1} A]).obj (DerivedCategory.Q.obj J)) =
      R((r)_*[ModuleCat.{u + 1} A]).map (adjk.unit.app (DerivedCategory.Q.obj J)) := by
    obtain ⟨I, hI, ρ, _, hρ⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      ((((k)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj J)
    have := hI
    have := hρ
    let z := ((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
      DerivedCategory.Q.map ρ
    let q := ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
      |>.mapHomologicalComplex (.up ℤ)).unit.app J ≫
      (((k)^*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map ρ
    let t := D((k)^*[ModuleCat.{u + 1} A]).map z ≫
      ((k)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app I
    have : IsIso z := by dsimp only [z]; infer_instance
    have : IsIso t := by dsimp only [t]; infer_instance
    have ht : adjk.unit.app (DerivedCategory.Q.obj J) ≫ t =
        DerivedCategory.Q.map q := open_transpose_Q A k J I ρ
    have hn := (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).naturality z
    dsimp only [Functor.comp_map] at hn
    have hr := comparison_naturality (r)_*[ModuleCat.{u + 1} A] (J := J) q
    have he := exchange_on_injective A k r p i sq I
    have hg := hΓ k r p i sq.toCommSq J I ρ
    rw [← DerivedCategory.Q.map_comp] at hg
    let m := (NatTrans.mapHomologicalComplex (θ k r p i sq.toCommSq).hom (.up ℤ)).app J ≫
      (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map ρ
    have hq :
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
          |>.mapHomologicalComplex (.up ℤ)).unit.app
          ((((r)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj J) ≫
        (((i)^*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map m ≫
        (NatTrans.mapHomologicalComplex
          (baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq) (.up ℤ)).app I =
      (((r)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map q := by
      ext n : 1
      change
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
            ((r)_*[ModuleCat.{u + 1} A].obj (J.X n)) ≫
          (i)^*[ModuleCat.{u + 1} A].map
            ((θ k r p i sq.toCommSq).hom.app (J.X n) ≫
              (p)_*[ModuleCat.{u + 1} A].map (ρ.f n)) ≫
          (baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app (I.X n) =
        (r)_*[ModuleCat.{u + 1} A].map
          ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k).unit.app
              (J.X n) ≫ (k)^*[ModuleCat.{u + 1} A].map (ρ.f n))
      rw [Functor.map_comp, Category.assoc]
      have hn := (baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).naturality (ρ.f n)
      dsimp only [Functor.comp_map] at hn
      erw [hn]
      erw [reassoc_of% (support_exchange A k r p i sq.toCommSq
        (θ k r p i sq.toCommSq) (J.X n) (hθ k r p i sq.toCommSq (J.X n)))]
      rw [Functor.map_comp]
    have hu := adji.unit.naturality
      ((((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).hom)
    dsimp only [Functor.id_map, Functor.comp_map] at hu
    have hm := open_transpose_Q A i
      ((((r)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj J)
      ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I) m
    apply (cancel_mono
      (R((r)_*[ModuleCat.{u + 1} A]).map t ≫
        (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso
          ((((k)^*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I)).hom)).mp
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ht, hr]
    dsimp only [t]
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hn, he]
    rw [halpha]
    simp only [Category.assoc]
    rw [← (D((i)^*[ModuleCat.{u + 1} A])).map_comp_assoc
      (R((p)_*[ModuleCat.{u + 1} A]).map z)
      ((((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom)]
    rw [← (D((i)^*[ModuleCat.{u + 1} A])).map_comp_assoc
      (gamma.hom.app (DerivedCategory.Q.obj J))]
    rw [← hg]
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% hu, reassoc_of% hm]
    rw [← DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    rw [hq]
  have hcompat (K : DerivedCategoryModule A U) :
      alpha.app K ≫ (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
        (D((k)_!open[ModuleCat.{u + 1} A]).obj K) =
      R((r)_*[ModuleCat.{u + 1} A]).map (adjk.unit.app K) := by
    obtain ⟨J, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
    have ha := alpha.naturality e.hom
    have hx := (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).naturality
      (D((k)_!open[ModuleCat.{u + 1} A]).map e.hom)
    have hu := adjk.unit.naturality e.hom
    dsimp only [Functor.comp_map, Functor.id_map] at ha hx hu
    apply (cancel_mono ((D((k)^*[ModuleCat.{u + 1} A]) ⋙
      R((r)_*[ModuleCat.{u + 1} A])).map
        (D((k)_!open[ModuleCat.{u + 1} A]).map e.hom))).mp
    dsimp only [Functor.comp_map]
    rw [Category.assoc, ← hx, ← Category.assoc, ← ha, Category.assoc, hJ]
    rw [← Functor.map_comp, hu, Functor.map_comp]
  exact iso_of_normalization adjk adji R((p)_*[ModuleCat.{u + 1} A])
    R((r)_*[ModuleCat.{u + 1} A]) gamma
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq) (fun K ↦ by
      simpa only [halpha, Category.assoc] using hcompat K)

end AlgebraicGeometry.Etale
