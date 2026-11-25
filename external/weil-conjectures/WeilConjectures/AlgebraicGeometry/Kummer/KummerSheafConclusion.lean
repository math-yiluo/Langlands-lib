/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerSheafPredicates

/-! # Concrete propositions for sheaf Kummer assembly -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt
attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ diagonalDerivedSingleCounit
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The normalized-boundary proposition over a fixed scheme `W`: `normalizedBoundaryTarget`
for the diagonal coefficient functors, the roots-of-unity tower and the Kummer roots
normalization. -/
def sheafKummerConclusion (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (S : DiagonalAb W)
    (Q : ∀ n, Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (δ : Ext.{u + 1} S ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf) 1)
    (sourceNorm : sheafKummerSourcePredicate ℓ W D S Q)
    (finiteClass : sheafKummerFinitePredicate ℓ W Q)
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj S) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S))
    : Prop :=
    normalizedBoundaryTarget ℓ (diagonalScalarExtension ℓ W) (diagonalForget ℓ W) D
      S ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf) δ
      (Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
      (fun n => (diagonalFiniteToPadic ℓ n W).obj (Q n))
      (fun n => (diagonalFiniteToPadic ℓ n W).obj
        (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) W)) sourceNorm
      (kummerRootNormalization ℓ W hW)
      finiteClass a

end AlgebraicGeometry.ProEtale
