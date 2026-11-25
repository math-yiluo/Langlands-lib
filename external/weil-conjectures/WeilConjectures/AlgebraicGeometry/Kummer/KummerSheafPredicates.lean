/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictTargetTransport

/-! # Predicate types for sheaf Kummer assembly -/

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

/-- The type of finite-class predicates: families of predicates on the degree-two `Ext` classes
from the finite quotients `Q n` to the Cartier lines. -/
def sheafKummerFinitePredicate (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (Q : ∀ n, Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))) : Type (u + 1) :=
  ∀ n, Ext.{u + 1} ((diagonalFiniteToPadic ℓ n W).obj (Q n))
    ((diagonalFiniteToPadic ℓ n W).obj
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W)) 2 → Prop

/-- The type of source-normalization predicates: families of predicates on isomorphisms from
the levels of `D.ordinary.E.obj S` to the finite quotients `Q n`. -/
def sheafKummerSourcePredicate (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (S : DiagonalAb W)
    (Q : ∀ n, Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))) : Type (u + 1) :=
  ∀ n, ((D.ordinary.E.obj S).obj (op n) ≅
    (diagonalFiniteToPadic ℓ n W).obj (Q n)) → Prop

end AlgebraicGeometry.ProEtale
