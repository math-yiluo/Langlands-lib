/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # The canonical direct-image unit on a coefficient module

Source: diagonal tower coefficient changes (1), ordinary coefficient units and their
universal right-derived comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
universe a v w u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

section Single
variable {A B : Type a} [Category.{v} A] [Category.{v} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  {F : A ⥤ B} [F.Additive]

/-- The specified universal derived unit on a single object.
Source: diagonal trace universal-unit normalization.
(blueprint: def-diagonal-coefficient-unit-push). -/
def singlePushComparison (D : DiagonalRightDerived F) (M : A) :
    (DerivedCategory.singleFunctor B 0).obj (F.obj M) ⟶
      D.R.obj ((DerivedCategory.singleFunctor A 0).obj M) :=
  DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
    D.η.app ((HomologicalComplex.single A (.up ℤ) 0).obj M)

/-- Naturality of the specified single-object derived unit.
Source: diagonal trace universal-unit normalization.
(blueprint: def-diagonal-coefficient-unit-push).
Proof: compose naturality of the single-complex isomorphism and the universal unit. -/
theorem singlePushComparison_naturality (D : DiagonalRightDerived F)
    {M N : A} (f : M ⟶ N) :
    (DerivedCategory.singleFunctor B 0).map (F.map f) ≫ singlePushComparison D N =
      singlePushComparison D M ≫ D.R.map ((DerivedCategory.singleFunctor A 0).map f) := by
  have hs := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.naturality f
  have hη := D.η.naturality ((HomologicalComplex.single A (.up ℤ) 0).map f)
  unfold singlePushComparison
  simp only [Category.assoc]
  change DerivedCategory.Q.map ((HomologicalComplex.single B (.up ℤ) 0).map (F.map f)) ≫
      DerivedCategory.Q.map _ ≫ D.η.app _ =
    DerivedCategory.Q.map _ ≫ D.η.app _ ≫
      D.R.map (DerivedCategory.Q.map ((HomologicalComplex.single A (.up ℤ) 0).map f))
  erw [← DerivedCategory.Q.map_comp_assoc, hs, DerivedCategory.Q.map_comp]
  simpa only [Category.assoc, Functor.comp_map] using
    congrArg (fun k => DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫ k) hη

end Single

section ExactSquare
variable {A B C D : Type a}
  [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  {F : A ⥤ B} {G : C ⥤ D} [F.Additive] [G.Additive]
  (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
  (ordinary : F ⋙ V ≅ U ⋙ G)

private theorem singleFactor (M : A) :
    (U.mapDerivedCategorySingleFunctor 0).hom.app M =
      U.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M) := by
  exact (Iso.inv_comp_eq (U.mapDerivedCategoryFactors.app _)).mp
    (U.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M)

/-- The full derived-unit square evaluated on a single coefficient object.
Source: diagonal trace universal-unit normalization.
(blueprint: def-diagonal-coefficient-unit-push).
Proof: evaluate the normalization on the single complex and cancel the canonical
single-complex comparisons. Their coherence is checked in each degree. -/
theorem singlePushComparison_square
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG ordinary) (M : A) :
    V.mapDerivedCategory.map (singlePushComparison RF M) ≫
        s.iso.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) =
      (V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (ordinary.hom.app M) ≫
          singlePushComparison RG (U.obj M) := by
  let P := (HomologicalComplex.single A (.up ℤ) 0).obj M
  have hn := s.normalization P
  unfold singlePushComparison
  rw [singleFactor U M, RG.R.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  have hη := RG.η.naturality
    ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M)
  change DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M)) ≫
      RG.η.app ((HomologicalComplex.single C (.up ℤ) 0).obj (U.obj M)) =
    RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≫ RG.R.map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M)) at hη
  erw [← hη]
  have hV := V.mapDerivedCategoryFactors.hom.naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  change V.mapDerivedCategory.map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)) ≫
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    V.mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj M)) ≫
      DerivedCategory.Q.map ((V.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)) at hV
  erw [reassoc_of% hV]
  rw [singleFactor V (F.obj M)]
  have hc :
      (V.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
        (NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M) =
      (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).hom.app (F.obj M) ≫
        (HomologicalComplex.single D (.up ℤ) 0).map (ordinary.hom.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app (U.obj M) := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f]
      dsimp [P, HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single]
      change V.map (𝟙 (F.obj M)) ≫ ordinary.hom.app M ≫
        G.map (𝟙 (U.obj M)) =
          (𝟙 (V.obj (F.obj M))) ≫
            ((𝟙 (V.obj (F.obj M))) ≫ ordinary.hom.app M ≫ (𝟙 _)) ≫ (𝟙 _)
      simp only [Category.id_comp, Category.comp_id]
      exact (congrArg₂ (fun k h => k ≫ ordinary.hom.app M ≫ h)
        (V.map_id (F.obj M)) (G.map_id (U.obj M))).trans
          ((Category.id_comp _).trans (Category.comp_id _))
    · simp [P, HomologicalComplex.singleMapHomologicalComplex,
        HomologicalComplex.single, hn]
  have hs : (DerivedCategory.singleFunctor D 0).map (ordinary.hom.app M) =
      DerivedCategory.Q.map
        ((HomologicalComplex.single D (.up ℤ) 0).map (ordinary.hom.app M)) := rfl
  rw [hs]
  have hq := congrArg DerivedCategory.Q.map hc
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k => V.mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj M)) ≫ k ≫
        RG.η.app ((HomologicalComplex.single C (.up ℤ) 0).obj (U.obj M))) hq

end ExactSquare

/-- The ordinary coefficient-unit adjunct, with its regular-module endpoints fixed.
Source: diagonal tower coefficient changes (1), coefficient one.
(blueprint: def-diagonal-coefficient-unit-push). -/
@[irreducible]
def coefficientOrdinaryUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u}) :
    Mod.regular (condensedRingObj Λ Y) ⟶
      (CondensedRing.lowerStar Λ (ProjectiveLine Y ↘ Y)).obj
        (Mod.regular (condensedRingObj Λ (ProjectiveLine Y))) :=
  (CondensedRing.upperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y)).homEquiv _ _
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (ProjectiveLine Y ↘ Y))).inv

/-- The ordinary coefficient-unit arrow is the structural coefficient map.
Source: diagonal tower coefficient changes (1), the unital coefficient normalization.
(blueprint: def-diagonal-coefficient-unit-push).
Proof: the ordinary pullback-adjunction unit-coherence theorem identifies its
underlying sheaf map with the structural condensed-coefficient map. -/
theorem coefficientOrdinaryUnit_underlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u}) :
    (coefficientOrdinaryUnit Λ Y).hom =
      condensedPushforwardHom Λ (ProjectiveLine Y ↘ Y) := by
  unfold coefficientOrdinaryUnit
  exact CondensedRing.homEquiv_εIso_inv_hom Λ (ProjectiveLine Y ↘ Y)

/-- The coefficient-unit arrow, before composing with a local derived class.
It uses the ordinary pullback adjunction and the given universal derived unit.
Source: diagonal tower coefficient changes (1).
(blueprint: def-diagonal-coefficient-unit-push). -/
@[irreducible]
def coefficientUnitPush
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u})
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ (ProjectiveLine Y ↘ Y))) :
    unit Λ Y ⟶ D.R.obj (unit Λ (ProjectiveLine Y)) :=
  (DerivedCategory.singleFunctor _ 0).map (coefficientOrdinaryUnit Λ Y) ≫
    singlePushComparison D (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))

/-- The canonical derived finite-unit adjunct, with fixed unit endpoints.
Source: diagonal tower coefficient changes (1), finite coefficient units.
(blueprint: def-diagonal-coefficient-unit-push). -/
@[irreducible]
def finiteUnitAdjunct (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    geoP1Unit A Y ⟶
      (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).obj (geoP1Unit A (ProjectiveLine Y)) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine Y ↘ Y)).homEquiv _ _
      (geoP1UnitPullback A (ProjectiveLine Y ↘ Y)).hom

/-- Adjunction of a finite local arrow, with fixed derived-unit endpoints.
Source: diagonal tower coefficient changes (1), finite coefficient adjunction.
(blueprint: def-diagonal-coefficient-unit-push). -/
@[irreducible]
def finiteAdjunct (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    {Z : DerivedCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine Y))
      (ModuleCat.{u + 1} A))} (z : geoP1Unit A (ProjectiveLine Y) ⟶ Z) :
    geoP1Unit A Y ⟶ (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).obj Z :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine Y ↘ Y)).homEquiv _ _
      ((geoP1UnitPullback A (ProjectiveLine Y ↘ Y)).hom ≫ z)

/-- Composing the unit adjunct with a pushed arrow computes its adjunct.
Source: diagonal tower coefficient changes (1), adjunction naturality.
(blueprint: def-diagonal-coefficient-unit-push).
Proof: apply right naturality of the canonical derived adjunction bijection. -/
theorem finiteUnitAdjunct_naturality (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    {Z : DerivedCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine Y))
      (ModuleCat.{u + 1} A))} (z : geoP1Unit A (ProjectiveLine Y) ⟶ Z) :
    finiteUnitAdjunct A Y ≫ (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map z =
      finiteAdjunct A Y z := by
  unfold finiteUnitAdjunct finiteAdjunct
  exact ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine Y ↘ Y)).homEquiv_naturality_right _ z).symm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
