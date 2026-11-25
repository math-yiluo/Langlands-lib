/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.AcyclicFlatProperCoefficientModel
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.AcyclicFlatProperCoefficientModel

/-! # Proper coefficient model equation with only direct-image K-flatness
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar

/-- Proper coefficient model equation with only direct-image K-flatness. -/
theorem ordinaryChartProperModelScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {W V : Scheme.{u}} (r : W ⟶ V) [IsProper r] [IsNoetherian W] [IsNoetherian V]
    (φ : A →+* B)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hDV : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C)) :
    (properCoefficientTensor φ V).map (properAcyclicComparison A r C) ≫
        (properCoefficientMap φ r).app (DerivedCategory.Q.obj C) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
          (scalarExtensionRepresentative φ W C) =
      scalarExtensionRepresentative φ V
          (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map (properCoefficientComplexMap φ r C) ≫
        properAcyclicComparison B r (coefficientExtendedComplex φ W C) := by
  let a : (upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ) ⊣
      (lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ) :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)
  let b : (upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ) ⊣
      (lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ) :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)
  let σ := TwoSquare.mk
    ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ))
    ((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ))
    ((upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ))
    ((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ))
    (scalarSheafPullbackComplexIso φ r).hom
  let θ := TwoSquare.mk (scalarExtension φ V)
    L(upperStar (ModuleCat.{u + 1} A) r) L(upperStar (ModuleCat.{u + 1} B) r)
    (scalarExtension φ W) (scalarPullbackIso φ r).hom
  let D := ((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C
  have hn : θ.app (DerivedCategory.Q.obj D) ≫
      (scalarExtension φ W).map (scalarGeometricRepresentative A r D) ≫
        scalarExtensionRepresentative φ W
          (((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj D) =
      L(upperStar (ModuleCat.{u + 1} B) r).map
          (scalarExtensionRepresentative φ V D) ≫
        scalarGeometricRepresentative B r
          (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj D) ≫
        DerivedCategory.Q.map (σ.app D) := by
    dsimp only [θ, σ, TwoSquare.mk]
    exact scalar_pullback_normalization φ r D hDV
  have hs : (scalarSheafPullbackComplexIso φ r).hom =
      complexTransformation (ProEtale.etaleSheafExtendScalars φ V)
        (upperStar (ModuleCat.{u + 1} B) r) (upperStar (ModuleCat.{u + 1} A) r)
        (ProEtale.etaleSheafExtendScalars φ W) (scalarSheafPullbackIso φ r).hom :=
    by
      dsimp only [scalarSheafPullbackComplexIso]
      exact complex_iso_transformation _ _ _ _ (scalarSheafPullbackIso φ r)
  have hm : (mateEquiv a b σ).app C = properCoefficientComplexMap φ r C := by
    dsimp only [σ]
    rw [hs]
    dsimp only [properCoefficientComplexMap, properSheafCoefficientMap]
    simpa only [complexTransformation, NatTrans.comp_app] using
      complex_mate (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
      (ProEtale.etaleSheafExtendScalars φ V) (ProEtale.etaleSheafExtendScalars φ W)
      (TwoSquare.mk (ProEtale.etaleSheafExtendScalars φ V)
        (upperStar (ModuleCat.{u + 1} A) r) (upperStar (ModuleCat.{u + 1} B) r)
        (ProEtale.etaleSheafExtendScalars φ W) (scalarSheafPullbackIso φ r).hom) C
  let E := (ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)
  let M := ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj D
  let τ := σ.app D ≫ E.map (a.counit.app C)
  have hc : L(upperStar (ModuleCat.{u + 1} A) r).map
        (properAcyclicComparison A r C) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).counit.app
        (DerivedCategory.Q.obj C) =
      scalarGeometricRepresentative A r D ≫ DerivedCategory.Q.map (a.counit.app C) := by
    exact geometric_counit_normalization A r C
  have hu :
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r).unit.app
          (DerivedCategory.Q.obj M) ≫
        R(lowerStar (ModuleCat.{u + 1} B) r).map
          (scalarGeometricRepresentative B r M) =
      DerivedCategory.Q.map (b.unit.app M) ≫ properAcyclicComparison B r
        (((upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj M) := by
    exact geometric_unit_normalization B r M
  have h₄ := (scalarRepresentativeTransformation φ W).naturality (a.counit.app C)
  simp only [Functor.comp_map] at h₄
  rw [scalarRepresentativeTransformation_app, scalarRepresentativeTransformation_app] at h₄
  have h₇ := (acyclicComparisonTransformation
    (lowerStar (ModuleCat.{u + 1} B) r)).naturality τ
  simp only [Functor.comp_map] at h₇
  rw [acyclicComparisonTransformation_app, acyclicComparisonTransformation_app] at h₇
  have hτ : DerivedCategory.Q.map τ =
      DerivedCategory.Q.map (σ.app D) ≫
        DerivedCategory.Q.map (E.map (a.counit.app C)) := by
    exact CategoryTheory.Functor.map_comp DerivedCategory.Q _ _
  rw [hτ] at h₇
  have hn' : DerivedCategory.Q.map (b.unit.app M) ≫
      DerivedCategory.Q.map
        (((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map τ) =
      DerivedCategory.Q.map (properCoefficientComplexMap φ r C) := by
    rw [← CategoryTheory.Functor.map_comp, ← hm]
    congr 1
    exact (mate_component a b σ C).symm
  exact mate_comparison
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r) θ
    (properAcyclicComparison A r C)
    (properAcyclicComparison B r (coefficientExtendedComplex φ W C))
    (scalarExtensionRepresentative φ V D) (scalarExtensionRepresentative φ W C)
    (scalarGeometricRepresentative A r D) (scalarGeometricRepresentative B r M)
    (scalarExtensionRepresentative φ W
      (((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj D))
    (properAcyclicComparison B r
      (((upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj M))
    (DerivedCategory.Q.map (a.counit.app C)) (DerivedCategory.Q.map (b.unit.app M))
    (DerivedCategory.Q.map (σ.app D))
    (DerivedCategory.Q.map (E.map (a.counit.app C)))
    (DerivedCategory.Q.map
      (((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map τ))
    (DerivedCategory.Q.map (properCoefficientComplexMap φ r C)) hc hu hn h₄
    (by simpa only [E, M, coefficientExtendedComplex, Functor.comp_obj,
      Functor.id_obj] using h₇) hn'

end AlgebraicGeometry.Etale
