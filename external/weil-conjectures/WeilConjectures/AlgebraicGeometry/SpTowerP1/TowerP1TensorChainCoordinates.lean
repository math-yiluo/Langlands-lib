/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1FixedTotalTensor
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-tensor-chain-coordinates).

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

/-- The signed total-complex tensor at the intrinsic level, as a named functor.
Source: Levels (blueprint: def-sp-p1-tensor-chain-coordinates). -/
def intrinsicTotal (T : Scheme.{u}) :
    CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology T) (SpTowerShriek.B l E T n)) ℤ ×
    CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology T) (SpTowerShriek.B l E T n)) ℤ ⥤
    CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology T) (SpTowerShriek.B l E T n)) ℤ :=
  SemilinearSections.totalTensor.{u + 1, u, u + 1}
    (ProEt.topology T) (SpTowerShriek.B l E T n)

/-- The fixed total tensor and its signed source inclusions are the existing ones.
Source: Levels (blueprint: def-sp-p1-tensor-chain-coordinates). -/
def fixedSummand (T : Scheme.{u}) (P Q : CochainComplex (FixedSheaves l E n T) ℤ)
    (i j k : ℤ) (h : i + j = k) :
    P.X i ⊗ Q.X j ⟶ ((fixedTotalTensor l E n T).obj (P, Q)).X k :=
  CochainComplex.ιMapBifunctor P Q (curriedTensor (FixedSheaves l E n T)) i j k h

/-- Intrinsic total tensor inclusions, retaining the section-model sign convention.
Source: Levels (blueprint: def-sp-p1-tensor-chain-coordinates). -/
def intrinsicSummand (T : Scheme.{u})
    (P Q : CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology T) (SpTowerShriek.B l E T n)) ℤ)
    (i j k : ℤ) (h : i + j = k) :
    SemilinearSections.ordinaryTensor.{u + 1, u, u + 1}
      (ProEt.topology T) (SpTowerShriek.B l E T n) (P.X i) (Q.X j) ⟶
        ((intrinsicTotal l E n T).obj (P, Q)).X k :=
  SemilinearSections.tensorSummand.{u + 1, u, u + 1}
    (ProEt.topology T) (SpTowerShriek.B l E T n) P Q i j k h

/-- Total-complex realization coordinates fixed on every signed tensor summand.
Source: Levels (blueprint: def-sp-p1-tensor-chain-coordinates). -/
structure TensorChainCoordinates (T : Scheme.{u}) extends TensorOrdinaryCoordinates l E n T where
  chain : ∀ P Q : CochainComplex (FixedSheaves l E n T) ℤ,
    ((realization l E n T).mapHomologicalComplex (.up ℤ)).obj
        ((fixedTotalTensor l E n T).obj (P, Q)) ⟶
      (intrinsicTotal l E n T).obj
        (((realization l E n T).mapHomologicalComplex (.up ℤ)).obj P,
          ((realization l E n T).mapHomologicalComplex (.up ℤ)).obj Q)
  summand : ∀ (P Q : CochainComplex (FixedSheaves l E n T) ℤ)
    (i j k : ℤ) (h : i + j = k),
    (realization l E n T).map (fixedSummand l E n T P Q i j k h) ≫
      (chain P Q).f k =
    (ordinary (P.X i) (Q.X j)).hom ≫ intrinsicSummand l E n T
      (((realization l E n T).mapHomologicalComplex (.up ℤ)).obj P)
      (((realization l E n T).mapHomologicalComplex (.up ℤ)).obj Q) i j k h

end AlgebraicGeometry.ProEtale.SpTowerP1
