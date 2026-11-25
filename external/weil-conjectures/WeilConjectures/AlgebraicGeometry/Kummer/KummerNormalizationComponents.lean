/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerPureKernelNormalizationStatement
import WeilConjectures.AlgebraicGeometry.Kummer.KummerComparedKernelTriangle
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalFiniteUnderlyingIsoLift

/-! # The three properties of the concrete Kummer coefficient record. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierProKummerUnit cartierProRootMap diagonalFiniteToPadic diagonalForget
  diagonalScalarExtension diagonalScalarAdjunction

/-- The actual coefficient record has the signed Kummer triangles. -/
theorem strict_kummer_kernel_triangles (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)] :
    (strictKummerNormalizationCoefficients ℓ W hW).Kernel ℓ := by
  unfold KummerNormalizationCoefficients.Kernel
  exact kummer_compared_kernel_triangle ℓ W hW

/-- Pure evaluation supplies the evaluation property of the actual coefficient record. -/
theorem strict_kummer_evaluation_triangles (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) :
    (strictKummerNormalizationCoefficients ℓ W hW).PureTriangles
      ℓ (diagonalScalarExtension ℓ W) (diagonalScalarAdjunction ℓ W) D η := by
  unfold KummerNormalizationCoefficients.PureTriangles
  intro H b
  exact diagonal_pure_evaluation_triangle ℓ W D η _ H b

/-- The actual coefficient record has the ordinary root-normalized scalar lift. -/
theorem strict_kummer_coefficient_lift (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) :
    (strictKummerNormalizationCoefficients ℓ W hW).FiniteLift := by
  unfold KummerNormalizationCoefficients.FiniteLift
  exact kummer_finite_kernel_lift ℓ W hW

end AlgebraicGeometry.ProEtale
