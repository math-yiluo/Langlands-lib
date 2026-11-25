/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
public import WeilConjectures.AlgebraicGeometry.InternalScalarTensorPullModels
import all WeilConjectures.AlgebraicGeometry.CanonicalCoefficientTensorNormalization

/-! # The exact pullback counit at the restricted regular coefficient -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Functor.mapDerivedCategory
universe v u₁ u₂ u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace CategoryTheory
variable {C : Type u₁} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {E : Type u₂} [Category.{v + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{v + 1} E]
omit [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C] in
private theorem coefficient_iso_hom (M : C) :
    (Functor.tensorModelCoefficientIso M).hom = 𝟙 _ := by
  unfold Functor.tensorModelCoefficientIso homotopySingleComparisonIso
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _

private theorem generic_coefficient_counit (F : C ⥤ E) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : C) (N : E) (e : F.obj M ≅ N) :
    let eH := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj M) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app M ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    F.leftDerivedFunctorCounit.app (Functor.tensorModelCoefficient M) ≫
        DerivedCategory.Qh.map eH.hom =
      F.singleFunctorCompLeftDerivedFunctorIso.hom.app M ≫
        (DerivedCategory.singleFunctor _ 0).map e.hom := by
  let c := F.singleFunctorCompLeftDerivedFunctorIso.app M ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e
  let eH := (F.mapHomotopyCategoryFactors (.up ℤ)).app
      ((CochainComplex.singleFunctor _ 0).obj M) ≪≫
    (HomotopyCategory.quotient _ (.up ℤ)).mapIso
      ((F.mapCochainComplexSingleFunctor 0).app M ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
  have h := Functor.tensorModelCoefficientIso_counit F M N e
  dsimp only at h
  rw [coefficient_iso_hom, coefficient_iso_hom, F.leftDerivedFunctor.map_id] at h
  erw [Category.id_comp, Category.id_comp] at h
  change c.inv ≫ F.leftDerivedFunctorCounit.app (Functor.tensorModelCoefficient M) =
    DerivedCategory.Qh.map eH.inv at h
  change F.leftDerivedFunctorCounit.app (Functor.tensorModelCoefficient M) ≫
    DerivedCategory.Qh.map eH.hom = c.hom
  apply (cancel_epi c.inv).mp
  rw [← Category.assoc, h, ← DerivedCategory.Qh.map_comp,
    Iso.inv_hom_id, DerivedCategory.Qh.map_id, Iso.inv_hom_id]
  rfl
end CategoryTheory

namespace AlgebraicGeometry.ProEtale.QuotientChange
set_option allowUnsafeReducibility true
attribute [local reducible] L CondensedRing.moduleObjectDerivedPullback

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

omit [IsCommMonObj Λ] in
private theorem regular_restriction_hom (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (scalarTensorRegularRestriction a T).hom =
      ((V₀ a T).mapDerivedCategorySingleFunctor 0).hom.app
        (Mod.regular (condensedRingObj Λ' T)) := by
  rw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
  rfl

section NativeUnit
-- Use the native module pullback and the same relative tensor structures as its unit.
attribute [local instance 21000] CondensedRing.monoidal_upperStar
attribute [local instance 20000] sheafBraidedCategory
attribute [local reducible] Mod.derivedMonoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local semireducible] DerivedCategory.monoidalClosed Mod.monoidalClosed

private theorem exact_unit (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom =
      (CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.hom.app
        (Mod.regular (condensedRingObj Λ Y)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv := by
  unfold CondensedRing.leftDerivedUpperStarUnitIso
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  have h := CategoryTheory.generic_coefficient_counit (CondensedRing.upperStar Λ f)
    (𝟙_ (Modules Λ Y)) (𝟙_ (Modules Λ X))
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm
  dsimp only at h
  exact h

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem restriction_pull_single (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules Λ' Y) :
    (CondensedRing.derivedComapUpperStarIso a f).inv.app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (V a X).map (((CondensedRing.upperStar Λ' f).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      ((V₀ a X).mapDerivedCategorySingleFunctor 0).hom.app
        ((CondensedRing.upperStar Λ' f).obj M) =
    (CondensedRing.upperStar Λ f).mapDerivedCategory.map
        (((V₀ a Y).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      ((CondensedRing.upperStar Λ f).mapDerivedCategorySingleFunctor 0).hom.app
        ((V₀ a Y).obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((CondensedRing.comapUpperStarIso a f).inv.app M) := by
  unfold CondensedRing.derivedComapUpperStarIso
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor
    (CondensedRing.upperStar Λ' f) (V₀ a X) (V₀ a Y ⋙ CondensedRing.upperStar Λ f)
    (CondensedRing.comapUpperStarIso a f).symm M]
  erw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor
    (V₀ a Y) (CondensedRing.upperStar Λ f) M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

omit [IsCommMonObj Λ] in
private theorem regular_restriction_iso (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    scalarTensorRegularRestriction a T =
      ((V₀ a T).mapDerivedCategorySingleFunctor 0).app
        (Mod.regular (condensedRingObj Λ' T)) := by
  apply Iso.ext
  exact regular_restriction_hom a T

-- The single-object comparison traverses several exact derived functor isomorphisms.
private theorem regular_pull_eq (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarTensorRegularPullIso a f =
      ((CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso).app (B₀ a Y) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (CondensedRing.residueOrdinaryRestrictedRegularPullIso Λ Λ' a f) := by
  apply Iso.ext
  simp only [← regularPullback₀_eq a f]
  unfold scalarTensorRegularPullIso
  dsimp only [id]
  simp only [regular_restriction_iso a Y, regular_restriction_iso a X]
  unfold scalarTensorRestrictPullIso RestrictedCoefficientMate.regularPullback₀
    Functor.singleFunctorCompLeftDerivedFunctorIso
  dsimp only [id]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  -- Normalize the mapped unit without rechecking the preceding comparison maps.
  conv_lhs =>
    arg 2; arg 2; arg 2
    rw [← (V a X).map_comp_assoc, exact_unit Λ' f]
  simp only [Functor.map_comp, Category.assoc]
  have hc : (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' f).inv.app
      ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ' Y))) ≫
      (CondensedRing.upperStar Λ' f).singleFunctorCompLeftDerivedFunctorIso.hom.app
        (Mod.regular (condensedRingObj Λ' Y)) =
      ((CondensedRing.upperStar Λ' f).mapDerivedCategorySingleFunctor 0).hom.app
        (Mod.regular (condensedRingObj Λ' Y)) := by
    change (CondensedRing.upperStar Λ' f).leftDerivedFunctorIsoMapDerivedCategory.inv.app _ ≫
      ((CondensedRing.upperStar Λ' f).leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫ _) = _
    exact Iso.inv_hom_id_app_assoc _ _ _
  erw [← (V a X).map_comp_assoc, hc]
  have hn := (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (((V₀ a Y).mapDerivedCategorySingleFunctor 0).inv.app
      (Mod.regular (condensedRingObj Λ' Y)))
  have hnX := ((V₀ a X).mapDerivedCategorySingleFunctor 0).hom.naturality
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ' f)).inv
  dsimp only [Functor.comp_map] at hn hnX
  erw [reassoc_of% hn]
  erw [hnX]
  erw [reassoc_of% restriction_pull_single a f (Mod.regular (condensedRingObj Λ' Y))]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(CondensedRing.upperStar Λ f).mapDerivedCategory.map_id, Category.id_comp]

end NativeUnit

/-- The coefficient pullback comparison commutes with the exact pullback counit.

Source: Stacks 07A6, 06YY; integral proper-base-change proof (1), (3),
the restricted regular coefficient in the scalar tensor-model normalization.
(auxiliary; not a blueprint node).

Proof. Express scalarTensorRegularRestriction as the exact restriction functor's
singleFunctor comparison. Expand scalarTensorRegularPullIso, replacing each exact
left-derived pullback by its mapDerivedCategory comparison. Naturality cancels
the Y restriction/single comparison and the exact restriction/pullback square.
The composition and natural-isomorphism identities for mapDerivedCategory on
single objects leave the singleFunctor comparison for ordinary pullback,
followed by the single image of restriction of the inverse ordinary unit.
This is residueOrdinaryRestrictedRegularPullIso: the native and transported
inverse units agree by expanding the scalar-extension transport, mapping the
identity of the regular module, and applying map_id. Thus the coefficient
comparison is F.singleFunctorCompLeftDerivedFunctorIso followed by single.mapIso e.
Apply Functor.tensorModelCoefficientIso_counit to F and e. This gives exactly
the displayed equality. The calculation uses only the regular coefficient
object, exact pullback and restriction; it involves no arbitrary homotopy
complex, scalar base-change comparison, or tensor presentation. -/
theorem scalar_regular_pull_counit (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let F := CondensedRing.upperStar Λ f
    let e := CondensedRing.residueOrdinaryRestrictedRegularPullIso Λ Λ' a f
    let eH := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj (B₀ a Y)) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app (B₀ a Y) ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    (scalarTensorRegularPullIso a f).inv ≫
      (L Λ f).map (Functor.tensorModelCoefficientIso (B₀ a Y)).hom ≫
      (pullCounit (Λ := Λ) f).app (Functor.tensorModelCoefficient (B₀ a Y)) =
      (Functor.tensorModelCoefficientIso (B₀ a X)).hom ≫
        DerivedCategory.Qh.map eH.inv := by
  dsimp only
  have h := Functor.tensorModelCoefficientIso_counit (CondensedRing.upperStar Λ f)
    (B₀ a Y) (B₀ a X)
    (CondensedRing.residueOrdinaryRestrictedRegularPullIso Λ Λ' a f)
  dsimp only at h
  rw [regular_pull_eq a f]
  unfold pullCounit
  dsimp only [id]
  exact h

end AlgebraicGeometry.ProEtale.QuotientChange
