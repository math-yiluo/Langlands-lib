/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedSingleUnit

/-!
# Exact adjunctions and single-object derived units

Source: Stacks 0A45 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace CategoryTheory.Adjunction
private theorem factorsh_complex {E F' : Type*} [Category E] [Category F'] [Abelian E] [Abelian F']
    [HasDerivedCategory E] [HasDerivedCategory F']
    (H : E ⥤ F') [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] (K : CochainComplex E ℤ) :
    H.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient E (.up ℤ)).obj K) =
    H.mapDerivedCategoryFactors.hom.app K := by
  rw [H.mapDerivedCategoryFactorsh_hom_app]
  change H.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj K)) ≫
    H.mapDerivedCategoryFactors.hom.app K ≫
    𝟙 (DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    DerivedCategory.Qh.map (𝟙 ((HomotopyCategory.quotient F' (.up ℤ)).obj
      ((H.mapHomologicalComplex (.up ℤ)).obj K))) = _
  erw [H.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := F')).map_id]
  change 𝟙 _ ≫ H.mapDerivedCategoryFactors.hom.app K ≫
    𝟙 (DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    𝟙 (DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K)) = _
  simp only [Category.id_comp, Category.comp_id]
  exact Category.comp_id _
private theorem single_unit_term
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (X : C) :
    (DerivedCategory.singleFunctor C 0).map (adj.unit.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C (.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj X))) ≫
      G.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient C (.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj X))) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj X))) := by
  rw [adj.mapHomotopyCategory_unit_app_quotient (.up ℤ)]
  rw [factorsh_complex F]
  change (DerivedCategory.singleFunctor C 0).map (adj.unit.app X) ≫
    (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X)) ≫
    G.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj X))) = _
  rw [factorsh_complex G]
  erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  erw [Functor.mapDerivedCategoryFactors_hom_naturality]
  erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
    DerivedCategory.Q.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors, Functor.comp_obj,
      CochainComplex.shiftFunctor_obj_X', Functor.id_obj, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
      Adjunction.mapHomologicalComplex_unit_app_f,
      HomologicalComplex.single_map_f_self]
    change (adj.unit.app X ≫ 𝟙 _) ≫ G.map (𝟙 (F.obj X)) ≫
      G.map (F.map (𝟙 X)) = adj.unit.app X
    simp only [F.map_id, G.map_id, Category.comp_id]
    exact Category.comp_id _
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X n hn).eq_of_src _ _

section
open MonoidalCategory
universe vC vD uC uD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{vC} C] [HasDerivedCategory.{vD} D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

private theorem exact_unit_single (adj : f ⊣ g) (X : C) :
    adj.derivedAdjunction.unit.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
      g.rightDerivedFunctor.map (f.singleFunctorCompLeftDerivedFunctorIso.hom.app X) ≫
      g.singleFunctorCompRightDerivedFunctorIso.hom.app (f.obj X) =
    (DerivedCategory.singleFunctor C 0).map (adj.unit.app X) := by
  let K := (HomotopyCategory.quotient C (.up ℤ)).obj
    ((CochainComplex.singleFunctor C 0).obj X)
  have hm := adj.mapDerivedCategoryAdjunction_unit_app_fac K
  have ht := single_unit_term f g adj X
  have hc : adj.mapDerivedCategoryAdjunction.unit.app
      (DerivedCategory.Qh.obj K) ≫
      g.mapDerivedCategory.map (f.mapDerivedCategoryFactorsh.hom.app K) =
    (DerivedCategory.singleFunctor C 0).map (adj.unit.app X) ≫
      (g.mapDerivedCategorySingleFunctor 0).inv.app (f.obj X) ≫
      g.mapDerivedCategory.map ((f.mapDerivedCategorySingleFunctor 0).inv.app X) ≫
      g.mapDerivedCategory.map (f.mapDerivedCategoryFactorsh.hom.app K) :=
    (cancel_mono (g.mapDerivedCategoryFactorsh.hom.app
      ((f.mapHomotopyCategory (.up ℤ)).obj K))).mp
      (by simpa only [Functor.comp_obj, Functor.id_obj, K, Functor.map_comp,
        Category.assoc] using hm.trans ht.symm)
  have hu : adj.mapDerivedCategoryAdjunction.unit.app
      (DerivedCategory.Qh.obj K) =
    (DerivedCategory.singleFunctor C 0).map (adj.unit.app X) ≫
      (g.mapDerivedCategorySingleFunctor 0).inv.app (f.obj X) ≫
      g.mapDerivedCategory.map ((f.mapDerivedCategorySingleFunctor 0).inv.app X) :=
    (cancel_mono (g.mapDerivedCategory.map
      (f.mapDerivedCategoryFactorsh.hom.app K))).mp
      (by simpa only [Category.assoc] using hc)
  have hv : adj.mapDerivedCategoryAdjunction.unit.app
      ((DerivedCategory.singleFunctor C 0).obj X) ≫
      g.mapDerivedCategory.map ((f.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (g.mapDerivedCategorySingleFunctor 0).hom.app (f.obj X) =
    (DerivedCategory.singleFunctor C 0).map (adj.unit.app X) := by
    change adj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj K) ≫
      g.mapDerivedCategory.map ((f.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (g.mapDerivedCategorySingleFunctor 0).hom.app (f.obj X) = _
    rw [hu]
    simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, g.mapDerivedCategory.map_id, Category.id_comp]
    exact Category.comp_id _
  simp only [Adjunction.mapDerivedCategoryAdjunction,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] at hv
  rw [← g.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc] at hv
  simpa only [Functor.singleFunctorCompLeftDerivedFunctorIso,
    Functor.singleFunctorCompRightDerivedFunctorIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj, Functor.id_obj,
    Functor.map_comp, Category.assoc] using hv
private theorem exact_unit_single_map (adj : f ⊣ g) (X : C) (Y : D)
    (c : f.obj X ⟶ Y) :
    adj.derivedAdjunction.unit.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
      g.rightDerivedFunctor.map (f.singleFunctorCompLeftDerivedFunctorIso.hom.app X ≫
        (DerivedCategory.singleFunctor D 0).map c) ≫
      g.singleFunctorCompRightDerivedFunctorIso.hom.app Y =
    (DerivedCategory.singleFunctor C 0).map (adj.homEquiv X Y c) := by
  rw [g.rightDerivedFunctor.map_comp]
  simp only [Category.assoc]
  have hn := g.singleFunctorCompRightDerivedFunctorIso.hom.naturality c
  simp only [Functor.comp_map] at hn
  rw [hn]
  rw [reassoc_of% exact_unit_single adj X]
  rw [Adjunction.homEquiv_apply, Functor.map_comp]
/-- For an exact adjoint pair, the derived unit on a single object becomes the
single of the underived adjunct under the canonical single comparisons.
Source: Stacks 0A45, derived support-Hom normalization
(auxiliary; not a blueprint node).

Proof: compute the homotopy adjunction unit on a single complex degreewise.
The quotient factorization identifies it with the termwise underived unit.
Cancel the left and right exact-derived comparison isomorphisms to identify
that derived unit. Naturality of the right single comparison then allows an
arbitrary morphism c after the left single comparison. This argument takes
place in the unbounded derived categories and assumes no flatness of objects. -/
theorem derivedSingleUnit_comp_comparison (adj : f ⊣ g) (X : C) (Y : D)
    (c : f.obj X ⟶ Y) :
    derivedSingleUnit adj X Y c ≫
      g.singleFunctorCompRightDerivedFunctorIso.hom.app Y =
    (DerivedCategory.singleFunctor C 0).map (adj.homEquiv X Y c) := by
  unfold derivedSingleUnit
  simpa only [Category.assoc] using exact_unit_single_map adj X Y c

end
end CategoryTheory.Adjunction
