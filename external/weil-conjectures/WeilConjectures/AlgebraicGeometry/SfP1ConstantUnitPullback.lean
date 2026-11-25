/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.SfP1ConstantUnitHom
import WeilConjectures.AlgebraicGeometry.SfP1UnitPullbackNativeHom
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Inverse image and the constant-unit comparison -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

attribute [local irreducible] DerivedCategory.singleFunctors upperStar lowerStar
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

attribute [local semireducible] projection
attribute [local implicit_reducible] projection projectiveLineDiagonalProjection

private theorem iso_transport_unit
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b : C} {x y : D} (e : a ≅ b) (j : x ≅ y)
    (q : F.obj a ⟶ x) (r : F.obj b ⟶ y)
    (h : F.map e.inv ≫ q = r ≫ j.inv) :
    q ≫ j.hom = F.map e.hom ≫ r := by
  rw [← cancel_epi (F.map e.inv), ← Category.assoc, h, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem native_unit_compat
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (leftDerivedUpperStarSingleConstantSheafIso B f (𝟙_ B)).hom ≫
        (singleFunctorObjUnitIso B X).hom =
      (upperStar B f).leftDerivedFunctor.map (singleFunctorObjUnitIso B Y).hom ≫
        (leftDerivedUpperStarUnitIso B f).hom := by
  exact iso_transport_unit (upperStar B f).leftDerivedFunctor
    (singleFunctorObjUnitIso B Y) (singleFunctorObjUnitIso B X)
    (leftDerivedUpperStarSingleConstantSheafIso B f (𝟙_ B)).hom
    (leftDerivedUpperStarUnitIso B f).hom
    (leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp B f)

/-- Inverse image preserves the specified constant-unit comparison.
Source: blueprint thm-amb-p1-adjunction.proof.md, constant-unit normalization.
(auxiliary; not a blueprint node).

Proof: identify constantUnit with singleFunctorObjUnitIso and the ordinary
constant inverse-image map with the native single-constant comparison. The native
unit formula after cancelling the two single-unit isomorphisms gives the equation. -/
theorem constantUnit_pullback
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFiniteUnitPullback A f).hom ≫ (constantUnit A X).hom =
      (ordinaryFinitePullback A f).map (constantUnit A Y).hom ≫
        (leftDerivedUpperStarDerivedTensorUnitIso f).hom := by
  rewrite [unitPullback_native_hom, constantUnit_hom, constantUnit_hom]
  exact native_unit_compat (ModuleCat.{u + 1} A) f

end AlgebraicGeometry.Etale.SfP1Transport
