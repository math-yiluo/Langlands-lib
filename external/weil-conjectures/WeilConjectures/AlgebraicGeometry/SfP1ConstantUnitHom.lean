/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
/-! # The canonical constant-unit comparison -/

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

private theorem constant_unit_hom_generic
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (T : Scheme.{u}) :
    ((DerivedCategory.singleFunctor _ 0).mapIso
        (Functor.Monoidal.εIso (constantSheaf T.smallEtaleTopology B)).symm ≪≫
      singleFunctorObjUnitIso B T).hom = (singleFunctorObjUnitIso B T).hom := by
  have hη : Functor.OplaxMonoidal.η (constantSheaf T.smallEtaleTopology B) = 𝟙 _ := by
    change (presheafToSheaf T.smallEtaleTopology B).map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
    simp
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.Monoidal.εIso_inv, hη, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The constant coefficient comparison is the native single-degree unit comparison.
Source: the definition of constantUnit and the monoidal unit of constant sheafification
in blueprint thm-amb-p1-adjunction.proof.md, first-coordinate unit normalization.
(auxiliary; not a blueprint node).

Proof: the oplax unit of constantSheaf is presheafToSheaf.map(identity) followed
by identity. Both are identities. The inverse of its monoidal unit iso is this
oplax unit, and the single-degree functor maps it to identity. The first factor
in constantUnit therefore cancels, leaving the stated single-degree comparison. -/
theorem constantUnit_hom
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (constantUnit A T).hom = (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T).hom := by
  unfold constantUnit
  exact constant_unit_hom_generic (ModuleCat.{u + 1} A) T

end AlgebraicGeometry.Etale.SfP1Transport
