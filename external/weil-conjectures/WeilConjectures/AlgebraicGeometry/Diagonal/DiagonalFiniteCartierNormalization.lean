/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictTargetTransport
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalCartierAdjunctUniqueness

/-! # Finite scalar normalization of the Cartier adjunct
Source: diagonal tower system proof, step (4).
(blueprint: lem-sfb-diagonal-finite-cartier-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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

/-- The full Cartier-adjunct equation gives exactly the finite scalar normalization.
Source: diagonal tower system proof, step (4), restriction after the full
residue-linear class comparison
(blueprint: lem-sfb-diagonal-finite-cartier-normalization).

Proof: the Cartier-adjunct uniqueness theorem identifies e with the canonical
residue-linear class. Its named family and the original canonical class agree
heterogeneously by definition. Apply congrArg to the exact-functor image and
then take HEq; unfolding the family gives precisely the original canonical class.
This shares the coefficient
structure comparison before the abstract assembly and does not infer class
equality from faithfulness of scalar forgetting. -/
theorem diagonal_finite_cartier_normalization (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    (hW : IsUnit (ℓ : Γ(diagonalSurface Y, ⊤))) (n : ℕ)
    (e : Ext.{u + 1}
      ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
        (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y)))
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)) 2)
    (he : kummerScalarAdjunct (A := DiagonalAb (diagonalSurface Y))
      (cartierForget (diagonalResidue.{u} ℓ n) (diagonalSurface Y))
      (cartierProIntegralGenerator (diagonalResidue.{u} ℓ n) (diagonalImmersion Y)) e =
      negativeExtProduct (diagonalIntegralBoundary Y)
        (kummerComparedUnit ℓ (diagonalSurface Y) hW n)) :
    HEq (exactFunctorExtImage (diagonalFiniteToPadic ℓ n (diagonalSurface Y)) e)
      (exactFunctorExtImage (diagonalFiniteToPadic ℓ n (diagonalSurface Y))
        (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1) (diagonalImmersion Y)
          (diagonalImmersion_cartier Y) (diagonalSurface_power_unit ℓ Y hY n))) := by
  have hc := diagonal_cartier_class_of_adjunct ℓ Y hY hW n e he
  unfold diagonalResidueClasses canonicalCartierClass at hc
  unfold cartierResidueReducedPro
  exact heq_of_eq (congrArg
    (fun x => exactFunctorExtImage (diagonalFiniteToPadic ℓ n (diagonalSurface Y)) x) hc)

end AlgebraicGeometry.ProEtale
