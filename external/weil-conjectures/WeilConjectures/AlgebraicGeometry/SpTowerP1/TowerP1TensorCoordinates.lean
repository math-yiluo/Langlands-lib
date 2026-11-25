/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1TensorChainCoordinates
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-tensor-derived-coordinates).

The coordinates retain the canonical associated-module-sheaf functor. Its tensor
comparison is fixed on scalar-unit pure tensors, on total-complex summands, and
on K-flat representatives. Thus the final level equations cannot be satisfied
by choosing unrelated isomorphisms of their endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
universe u

namespace AlgebraicGeometry.ProEtale.SpTowerP1
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)]
/-- Fixed-scalar K-flat tensor model, with its standard localization comparison.
Source: Levels (blueprint: def-sp-p1-tensor-derived-coordinates). -/
def fixedTensorModel (T : Scheme.{u}) (P Q : CochainComplex (FixedSheaves l E n T) ℤ)
    (hP : (HomologicalComplex.quasiIso (FixedSheaves l E n T) (.up ℤ)).kFlat P) :
    ((ProEtale.derivedTensor
      (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) T).obj
        (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj ((fixedTotalTensor l E n T).obj (P, Q)) :=
  DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P Q hP

/-- Derived tensor realization fixed on every K-flat representative, including total
summands and exact localization factors. The data cannot be an arbitrary endpoint iso.
Source: Levels (blueprint: def-sp-p1-tensor-derived-coordinates). -/
structure TensorCoordinates (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    extends TensorChainCoordinates l E n T where
  derived : Functor.uncurry.obj
      (ProEtale.derivedTensor
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) T) ⋙
      (realization l E n T).mapDerivedCategory ≅
    ((realization l E n T).mapDerivedCategory.prod
      (realization l E n T).mapDerivedCategory) ⋙ ((b.calculus T).levelClosed n).tensor
  preserves_kflat : ∀ P : CochainComplex (FixedSheaves l E n T) ℤ,
    (HomologicalComplex.quasiIso (FixedSheaves l E n T) (.up ℤ)).kFlat P →
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology T) (R := SpTowerShriek.B l E T n)
        (((realization l E n T).mapHomologicalComplex (.up ℤ)).obj P)
  representative : ∀ (P Q : CochainComplex (FixedSheaves l E n T) ℤ)
    (hP : (HomologicalComplex.quasiIso (FixedSheaves l E n T) (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso (FixedSheaves l E n T) (.up ℤ)).kFlat Q),
    (realization l E n T).mapDerivedCategory.map
      (fixedTensorModel l E n T P Q hP).hom ≫
      (realization l E n T).mapDerivedCategoryFactors.hom.app
        ((fixedTotalTensor l E n T).obj (P, Q)) ≫
      DerivedCategory.Q.map (chain P Q) ≫
      (SemilinearSections.tensorModelIso.{u + 1, u, u + 1} (ProEt.topology T)
        (SpTowerShriek.B l E T n)
        ((b.calculus T).levelClosed n) ((b.calculus T).levelTensorModels n)
        (((realization l E n T).mapHomologicalComplex (.up ℤ)).obj P)
        (((realization l E n T).mapHomologicalComplex (.up ℤ)).obj Q)
        (preserves_kflat P hP) (preserves_kflat Q hQ)).hom =
    derived.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      ((b.calculus T).levelClosed n).tensor.map
        (Prod.mkHom ((realization l E n T).mapDerivedCategoryFactors.hom.app P)
          ((realization l E n T).mapDerivedCategoryFactors.hom.app Q))

end AlgebraicGeometry.ProEtale.SpTowerP1
