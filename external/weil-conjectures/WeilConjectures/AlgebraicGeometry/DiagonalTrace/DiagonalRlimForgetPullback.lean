/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimForgetUnit

/-! # Forgetting constant scalars commutes with inverse image -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- The constant-scalar forgetful functor commutes with inverse image.

Source: Stacks Project, Modules on Sites, Tag 03D3.
Proof: use the explicit comparison constructed for the normalized unit.
Scalar forgetting preserves left Kan extensions and sheafification; their
canonical comparison isomorphisms compose to the required natural isomorphism.
This construction also covers the empty site and the zero sheaf.
(blueprint: new-sfb-diagonal-rlim-forget-pullback). -/
theorem diagonalRlimForgetPullback (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Nonempty (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f ⋙ diagonalForget l X ≅
      diagonalForget l S ⋙ upperStar AddCommGrpCat.{u + 1} f) := by
  exact ⟨forgetPullbackIso l f⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
