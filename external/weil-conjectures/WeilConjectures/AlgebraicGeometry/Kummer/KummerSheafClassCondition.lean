/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerSheafPredicates

/-! # Scalar-adjunct proposition for sheaf Kummer assembly -/

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

/-- The exact scalar-adjunct implication used in finite normalization.
This is the universal implication for the full residue-linear class, followed by
its actual exact-functor image. It contains no existence assertion or chosen data. -/
def sheafKummerClassCondition (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    (S : DiagonalAb W)
    (Q : ∀ n, Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (g : ∀ n, S ⟶ (cartierForget (diagonalResidue.{u} ℓ n) W).obj (Q n))
    (δ : Ext.{u + 1} S ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf) 1)
    (finiteClass : sheafKummerFinitePredicate ℓ W Q)
    : Prop :=
  ∀ n (e : Ext.{u + 1} (Q n)
        (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) W) 2),
      kummerScalarAdjunct (A := DiagonalAb W)
        (cartierForget (diagonalResidue.{u} ℓ n) W) (g n) e =
        negativeExtProduct δ (kummerComparedUnit ℓ W hW n) →
      finiteClass n (exactFunctorExtImage (diagonalFiniteToPadic ℓ n W) e)

end AlgebraicGeometry.ProEtale
