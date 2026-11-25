/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictAdjunctData
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerPureKernelNormalizationStatement
import WeilConjectures.AlgebraicGeometry.Kummer.KummerNormalizationComponents

/-! # Identification and normalization of the surviving Kummer cohomology
Source: diagonal tower system proof, steps (3) and (4).
(blueprint: lem-sfb-strict-kummer-pure-kernel-normalization). -/

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

/-- Identify the surviving cohomology with roots, including its scalar action
and the unit equation, after a pure strict-system comparison has been supplied.
There is no assertion here that such a comparison exists.

Source: diagonal tower system proof, step (3), kernel and transitions, and
step (4), Kummer-unit calculation
(blueprint: lem-sfb-strict-kummer-pure-kernel-normalization).

Proof: on a common flat K-flat resolution, compare positive prime-power
reduction with the two-term coefficient resolution. Its kernel is the roots
sheaf by Kummer exactness and exact site comparison. The resolution transition
is multiplication by ell in degree minus one and identity in degree zero;
its kernel transition is the actual power-ell roots transition. Apply cohomology
to b and compose its inverse with this kernel identification. This defines
roots on H; naturality of cohomology gives the entire tower identification.
The coefficient action on the surviving kernel is the quotient action through
Z/ell^(n+1). Its canonical identification with the finite Tate line therefore
lifts uniquely to the p-adic-linear isomorphism t, and forgetting it is exactly
roots followed by cartierProRootMap. To fix the sign choose the negative kernel
identification, consistently for all levels. The complexes equation of eta on
the same resolution identifies its unshifted quotient unit with the positive
Kummer boundary, preceded by comparison on units. Shift once and insert the
inverse shift-addition comparison. The negative kernel identification gives
the negative of that shifted class, which is the displayed equation. A change
of the supplied b transports roots and t by its induced cohomology
isomorphism; no equation is asserted for independently chosen roots and t.
No derived isomorphism is constructed in this step, nor is equality of derived
arrows detected levelwise. The computation works at n=0, ell=2, and for the
zero sheaf without changing signs or dividing by two. -/
theorem strict_kummer_pure_kernel_normalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) :
  strictKummerPureKernelNormalizationStatement ℓ W hW D η := by
  exact kummer_normalization_of_coefficients
    (A := DiagonalAb W) (B := DiagonalMod ℓ W)
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W)
    (catA := inferInstanceAs (Category (DiagonalAb W)))
    (catB := inferInstanceAs (Category (DiagonalMod ℓ W)))
    (hDerA := inferInstanceAs (HasDerivedCategory.{u + 1} (DiagonalAb W)))
    (hDerSys := inferInstanceAs (HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)))
    (hSys := inferInstanceAs (HasExt.{u + 1} (DiagonalSystems ℓ W)))
    (strictKummerNormalizationCoefficients ℓ W hW)
    ℓ (diagonalScalarExtension ℓ W) (diagonalScalarAdjunction ℓ W) D η
    (strict_kummer_kernel_triangles ℓ W hW)
    (strict_kummer_evaluation_triangles ℓ W hW D η)
    (strict_kummer_coefficient_lift ℓ W hW)

end AlgebraicGeometry.ProEtale
