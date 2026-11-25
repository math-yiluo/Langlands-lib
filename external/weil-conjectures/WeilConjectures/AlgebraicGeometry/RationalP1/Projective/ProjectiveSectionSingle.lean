/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition
public import WeilConjectures.CategoryTheory.Right.RightDerivedSingleH0
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.RightDerivedSingleCounit
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectivePullSectionSingle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace CategoryTheory.Adjunction
section SingleCounit
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
open MonoidalCategory Abelian
variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

/-- Transport the single-object counit along the exact-left-derived comparison. -/
private theorem single_leftDerived_counit (a : L ⊣ R) (M : D) :
    L.leftDerivedFunctor.map (R.singleRightDerivedUnit.app M) ≫
      a.derivedAdjunction.counit.app ((DerivedCategory.singleFunctor D 0).obj M) =
    L.singleFunctorCompLeftDerivedFunctorIso.hom.app (R.obj M) ≫
      (DerivedCategory.singleFunctor D 0).map (a.counit.app M) := by
  let e := L.leftDerivedFunctorIsoMapDerivedCategory
  have hc := a.single_rightDerived_counit M
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at hc
  apply (cancel_epi (e.inv.app
    ((DerivedCategory.singleFunctor C 0).obj (R.obj M)))).1
  have hn := e.inv.naturality (R.singleRightDerivedUnit.app M)
  dsimp only [Functor.comp_obj] at hn
  rw [← Category.assoc]
  erw [← hn]
  rw [Category.assoc]
  change _ = e.inv.app _ ≫
    (e.hom.app _ ≫ (L.mapDerivedCategorySingleFunctor 0).hom.app (R.obj M)) ≫ _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact hc

end SingleCounit
end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
public abbrev derivedAdj {X S : Scheme.{u}} (f : X ⟶ S) :=
  CondensedRing.derivedUpperStarLowerStarAdjunction Λ f
public def ordinarySection (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    CondensedRing.upperStar Λ f ⋙ CondensedRing.upperStar Λ (diagonalImmersion Y) ≅ 𝟭 _ :=
  (CondensedRing.upperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
    CondensedRing.upperStarCongr Λ h ≪≫
      CondensedRing.upperStarId Λ (ProjectiveLine Y)
public def derivedSection (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    (CondensedRing.upperStar Λ f).leftDerivedFunctor ⋙
      (CondensedRing.upperStar Λ (diagonalImmersion Y)).leftDerivedFunctor ≅
      𝟭 (DerivedCategory (Modules Λ (ProjectiveLine Y))) := by
  have e := pullSectionIso Λ Y f h
  exact e
private theorem derivedAdj_eq {X S : Scheme.{u}} (f : X ⟶ S) :
    derivedAdj Λ f = (CondensedRing.upperStarLowerStarAdjunction Λ f).derivedAdjunction := by
  rfl

private theorem ordinarySection_eq (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    ordinarySection Λ Y f h =
      (CondensedRing.upperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
        CondensedRing.upperStarCongr Λ h ≪≫
          CondensedRing.upperStarId Λ (ProjectiveLine Y) := by
  rfl

private theorem derivedSection_eq (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    derivedSection Λ Y f h = pullSectionIso Λ Y f h := by
  rfl

-- Match the two condensed-module single comparisons without unfolding their constructions.
private theorem section_single_pull (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (M : Modules Λ (ProjectiveLine Y)) :
    (derivedSection Λ Y f h).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj M) =
      (CondensedRing.upperStar Λ (diagonalImmersion Y)).leftDerivedFunctor.map
        ((CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.hom.app M) ≫
      (Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ (diagonalImmersion Y))).hom.app
          ((CondensedRing.upperStar Λ f).obj M) ≫
      (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
        ((ordinarySection Λ Y f h).hom.app M) := by
  rw [derivedSection_eq, ordinarySection_eq]
  exact projective_pull_section_single Λ Y f h M

set_option synthInstance.maxSize 4096 in
-- Elaborating the condensed-module derived comparisons needs a larger budget.
private theorem single_counit {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ X) :
    (CondensedRing.upperStar Λ f).leftDerivedFunctor.map
        ((CondensedRing.lowerStar Λ f).singleRightDerivedUnit.app M) ≫
      (derivedAdj Λ f).counit.app
        ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) =
    (CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.hom.app
        ((CondensedRing.lowerStar Λ f).obj M) ≫
      (DerivedCategory.singleFunctor (Modules Λ X) 0).map
        ((CondensedRing.upperStarLowerStarAdjunction Λ f).counit.app M) := by
  rw [derivedAdj_eq Λ f]
  exact (CondensedRing.upperStarLowerStarAdjunction Λ f).single_leftDerived_counit M

private theorem adjunct_comparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (a' : L' ⊣ R') (S : C ⥤ C') (T : D ⥤ D')
    (c : S ⋙ L' ⟶ L ⋙ T) (v : R ⋙ S ⟶ T ⋙ R')
    (hc : ∀ N, L'.map (v.app N) ≫ a'.counit.app (T.obj N) =
      c.app (R.obj N) ≫ T.map (a.counit.app N))
    (M : C) (N : D) (f : L.obj M ⟶ N) :
    a'.homEquiv _ _ (c.app M ≫ T.map f) = S.map (a.homEquiv M N f) ≫ v.app N := by
  apply (a'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, a'.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_symm_apply, hc, ← Category.assoc]
  have hn := c.naturality (a.homEquiv M N f)
  dsimp only [Functor.comp_map] at hn
  rw [hn, Category.assoc, ← T.map_comp]
  have he : L.map (a.homEquiv M N f) ≫ a.counit.app N = f := by
    simpa only [Adjunction.homEquiv_symm_apply] using (a.homEquiv M N).symm_apply_apply f
  rw [he]

set_option synthInstance.maxSize 4096 in
-- Elaborating the condensed-module derived comparisons needs a larger budget.
private theorem single_adjunct {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ S) (N : Modules Λ X)
    (c : (CondensedRing.upperStar Λ f).obj M ⟶ N) :
    (derivedAdj Λ f).homEquiv _ _
        ((CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.hom.app M ≫
          (DerivedCategory.singleFunctor (Modules Λ X) 0).map c) =
      (DerivedCategory.singleFunctor (Modules Λ S) 0).map
          ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv M N c) ≫
        (CondensedRing.lowerStar Λ f).singleRightDerivedUnit.app N := by
  exact adjunct_comparison (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (derivedAdj Λ f) (DerivedCategory.singleFunctor (Modules Λ S) 0)
    (DerivedCategory.singleFunctor (Modules Λ X) 0)
    (CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.hom
    (CondensedRing.lowerStar Λ f).singleRightDerivedUnit (single_counit Λ f) M N c

private theorem conjugate_id_hom {C : Type*} [Category C] {L R : C ⥤ C}
    (a : L ⊣ R) (e : L ≅ 𝟭 C) (X : C) :
    (conjugateIsoEquiv Adjunction.id a e).hom.app X =
      a.homEquiv X X (e.hom.app X) := by
  have h := unit_conjugateEquiv Adjunction.id a e.hom X
  simpa only [Functor.id_obj, Adjunction.id_unit, NatTrans.id_app, Category.id_comp,
    conjugateIsoEquiv_apply_hom, Adjunction.homEquiv_apply] using h

private theorem composite_comparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {K : D ⥤ C} {V : C ⥤ D}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {K' : D' ⥤ C'} {V' : C' ⥤ D'}
    (a : L ⊣ R) (b : K ⊣ V) (a' : L' ⊣ R') (b' : K' ⊣ V')
    (S : C ⥤ C') (T : D ⥤ D')
    (c₁ : S ⋙ L' ⟶ L ⋙ T) (c₂ : T ⋙ K' ⟶ K ⋙ S)
    (v₁ : R ⋙ S ⟶ T ⋙ R') (v₂ : V ⋙ T ⟶ S ⋙ V')
    (M N : C) (f : K.obj (L.obj M) ⟶ N)
    (h₁ : a'.homEquiv _ _ (c₁.app M ≫ T.map (b.homEquiv _ _ f)) =
      S.map (a.homEquiv _ _ (b.homEquiv _ _ f)) ≫ v₁.app (V.obj N))
    (h₂ : b'.homEquiv _ _ (c₂.app (L.obj M) ≫ S.map f) =
      T.map (b.homEquiv _ _ f) ≫ v₂.app N) :
    S.map (a.homEquiv _ _ (b.homEquiv _ _ f)) ≫ v₁.app (V.obj N) ≫
        R'.map (v₂.app N) =
      a'.homEquiv _ _ (b'.homEquiv _ _
        (K'.map (c₁.app M) ≫ c₂.app (L.obj M) ≫ S.map f)) := by
  rw [b'.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  rw [h₂]
  conv_rhs => rw [← Category.assoc, a'.homEquiv_naturality_right, h₁]
  rw [Category.assoc]

private theorem section_comparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {K : D ⥤ C} {V : C ⥤ D}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {K' : D' ⥤ C'} {V' : C' ⥤ D'}
    (a : L ⊣ R) (b : K ⊣ V) (a' : L' ⊣ R') (b' : K' ⊣ V')
    (S : C ⥤ C') (T : D ⥤ D')
    (c₁ : S ⋙ L' ⟶ L ⋙ T) (c₂ : T ⋙ K' ⟶ K ⋙ S)
    (v₁ : R ⋙ S ⟶ T ⋙ R') (v₂ : V ⋙ T ⟶ S ⋙ V')
    (e : L ⋙ K ≅ 𝟭 C) (e' : L' ⋙ K' ≅ 𝟭 C') (M : C)
    (hs : e'.hom.app (S.obj M) =
      K'.map (c₁.app M) ≫ c₂.app (L.obj M) ≫ S.map (e.hom.app M))
    (h₁ : a'.homEquiv _ _ (c₁.app M ≫ T.map (b.homEquiv _ _ (e.hom.app M))) =
      S.map (a.homEquiv _ _ (b.homEquiv _ _ (e.hom.app M))) ≫ v₁.app (V.obj M))
    (h₂ : b'.homEquiv _ _ (c₂.app (L.obj M) ≫ S.map (e.hom.app M)) =
      T.map (b.homEquiv _ _ (e.hom.app M)) ≫ v₂.app M) :
    S.map ((conjugateIsoEquiv Adjunction.id (a.comp b) e).hom.app M) ≫
        v₁.app (V.obj M) ≫ R'.map (v₂.app M) =
      (conjugateIsoEquiv Adjunction.id (a'.comp b') e').hom.app (S.obj M) := by
  rw [conjugate_id_hom, conjugate_id_hom, hs]
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  exact composite_comparison a b a' b' S T c₁ c₂ v₁ v₂ M M (e.hom.app M) h₁ h₂

set_option synthInstance.maxSize 4096 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Elaborating the condensed-module derived comparisons needs a larger budget.
/-- Single-complex derived section compatibility.
-/
theorem projective_section_single (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (M : Modules Λ (ProjectiveLine Y)) :
    (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
          ((conjugateIsoEquiv Adjunction.id
            ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
              (CondensedRing.upperStarLowerStarAdjunction Λ (diagonalImmersion Y)))
            (ordinarySection Λ Y f h)).hom.app M) ≫
        (CondensedRing.lowerStar Λ f).singleRightDerivedUnit.app
          ((CondensedRing.lowerStar Λ (diagonalImmersion Y)).obj M) ≫
      (CondensedRing.lowerStar Λ f).rightDerivedFunctor.map
        ((CondensedRing.lowerStar Λ (diagonalImmersion Y)).singleRightDerivedUnit.app M) =
      (conjugateIsoEquiv Adjunction.id
        ((derivedAdj Λ f).comp (derivedAdj Λ (diagonalImmersion Y)))
        (derivedSection Λ Y f h)).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj M) := by
  refine section_comparison
    (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ (diagonalImmersion Y))
    (derivedAdj Λ f) (derivedAdj Λ (diagonalImmersion Y))
    (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0)
    (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0)
    (CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.hom
    (CondensedRing.upperStar Λ (diagonalImmersion Y)).singleFunctorCompLeftDerivedFunctorIso.hom
    (CondensedRing.lowerStar Λ f).singleRightDerivedUnit
    (CondensedRing.lowerStar Λ (diagonalImmersion Y)).singleRightDerivedUnit
    (ordinarySection Λ Y f h) (derivedSection Λ Y f h) M ?_ ?_ ?_
  · exact section_single_pull Λ Y f h M
  · exact single_adjunct Λ f M
      ((CondensedRing.lowerStar Λ (diagonalImmersion Y)).obj M) _
  · exact single_adjunct Λ (diagonalImmersion Y)
      ((CondensedRing.upperStar Λ f).obj M) M _
end AlgebraicGeometry.ProEtale.RationalP1
