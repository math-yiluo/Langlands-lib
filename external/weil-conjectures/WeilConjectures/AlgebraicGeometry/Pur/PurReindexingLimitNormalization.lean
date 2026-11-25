/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurCompletedReindexingData
import WeilConjectures.AlgebraicGeometry.Pur.PurCompletedModuleReindexing
import all WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # PurReindexingLimitNormalization
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem reindexing_unit
    {C D E B : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [Category E] [Abelian E] [HasDerivedCategory E]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (F : C ⥤ D) [F.Additive] (H : C ⥤ E) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (P : D ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (G : E ⥤ B) [G.Additive]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions E]
    [H.PreservesKInjectiveComplexes] (beta : F ⋙ P ≅ H ⋙ G) :
    let b := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F P).symm ≪≫
      Functor.rightDerivedFunctorNatIso beta ≪≫
      Functor.rightDerivedFunctorCompIso H G ≪≫
      Functor.isoWhiskerRight H.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor
    ∀ (I : CochainComplex C ℤ), I.IsKInjective →
      P.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫
        b.hom.app (DerivedCategory.Q.obj I) ≫
        G.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
      P.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) ≫
        G.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj I) := by
  intro b I hI
  have := hI
  have hn :=
    AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.squareComparison_normalized
      F H P G beta I
  change P.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫
    b.hom.app (DerivedCategory.Q.obj I) ≫
    G.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
    P.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) ≫
      G.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj I)
  rw [Functor.rightDerivedFunctorUnitQ_eq, Functor.rightDerivedFunctorUnitQ_eq]
  apply (cancel_mono
    (G.rightDerivedFunctorObjQIso ((H.mapHomologicalComplex (.up ℤ)).obj I)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change b.hom.app (DerivedCategory.Q.obj I) ≫ _ ≫ _ =
    P.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).hom ≫
      P.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) at hn
  calc
    P.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).inv ≫
        (b.hom.app (DerivedCategory.Q.obj I) ≫
          G.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) ≫
          (G.rightDerivedFunctorObjQIso ((H.mapHomologicalComplex (.up ℤ)).obj I)).hom) =
        P.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).inv ≫
          (P.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).hom ≫
            P.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I)) := by
              rw [hn]
    _ = P.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) := by
          simp only [← P.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id,
            CategoryTheory.Functor.map_id, Category.id_comp]

-- The ordinary mate simplification exposes the canonical projection equation.
end AlgebraicGeometry.Scheme
