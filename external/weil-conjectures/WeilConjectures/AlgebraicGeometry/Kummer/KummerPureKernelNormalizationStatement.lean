/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictAdjunctData
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerPureKernelNormalizationData

/-! # The concrete Kummer normalization proposition. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierProKummerUnit cartierProRootMap diagonalFiniteToPadic diagonalForget
  diagonalScalarExtension diagonalScalarAdjunction

/-- The actual coefficient data of the concrete Kummer normalization theorem.
All fields are the original explicit constructions. -/
def strictKummerNormalizationCoefficients (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) :
    KummerNormalizationCoefficients (hA := kummerAbHasExt W) (diagonalForget ℓ W)
      (fun n ↦ Sheaf (Scheme.ProEt.topology W)
        (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))) where
  catC := fun n ↦ inferInstance
  TateF := fun n ↦ diagonalFiniteToPadic ℓ n W
  V := fun n ↦ cartierForget (diagonalResidue.{u} ℓ n) W
  M := (comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf
  R := Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime)
  P := fun n ↦ geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
    (cartierResidue_cast ℓ (n + 1)) W
  κ := fun n ↦ kummerComparedUnit ℓ W hW n
  rootNorm := kummerRootNormalization ℓ W hW
  σ := fun n ↦ diagonalFiniteForgetIso ℓ n W
  rootMap := fun n ↦ cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
    (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
    (by simpa using hW.pow (n + 1))

/-- The exact concrete specialization of KummerPureKernelNormalization, using
shared coefficients. Expanding the two real definitions gives the old concrete
conclusion. No hypothesis or conclusion changes and no data is chosen. -/
def strictKummerPureKernelNormalizationStatement (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) : Prop :=
  (strictKummerNormalizationCoefficients ℓ W hW).Normalized
    ℓ (diagonalScalarExtension ℓ W) (diagonalScalarAdjunction ℓ W) D η

end AlgebraicGeometry.ProEtale
