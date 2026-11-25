/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTransitionUnit

/-! # The ordinary quotient transition and the tensor units

The unit of ordinary scalar extension along `R → R_(n+1)`, followed by the quotient transition,
is the unit along `R → R_n`: both send a section `x` to `1 ⊗ x`.

Source: Stacks Project, Tags 03EK and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The unit of scalar extension along `R → R_(n+1)` followed by the quotient transition is
the unit along `R → R_n`, up to the identification of the composite restriction: both send
`x` to `1 ⊗ x`. -/
theorem completedAdicChangeQuotientTransition_unit
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (N : CompletedAdicModules X d) :
    (pbcScalarAdjunction (completedAdicCommProjection X d (n + 1))).unit.app N ≫
        (pbcRestrict (completedAdicCommProjection X d (n + 1))).map
          ((completedAdicChangeQuotientTransition X d n).app N) =
      (pbcScalarAdjunction (completedAdicCommProjection X d n)).unit.app N ≫
        (pbcRestrictComp (completedAdicCommProjection X d (n + 1))
          (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))
          (completedAdicCommProjection X d n)
          (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n))).inv.app
            ((completedAdicChange X (completedAdicCommProjection X d n)).obj N) := by
  exact SheafOfModules.changeOfRingsTransitionOfEq_unit (completedAdicCommProjection X d (n + 1))
    (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))
    (completedAdicCommProjection X d n)
    (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n))
    (completedAdicChangeData X (completedAdicCommProjection X d (n + 1))).choose_spec.choose
    (completedAdicChangeData X
      (completedAdicCommProjection X d (n + 1))).choose_spec.choose_spec.choose
    (completedAdicChangeData X (completedAdicCommProjection X d n)).choose_spec.choose
    (completedAdicChangeData X (completedAdicCommProjection X d n)).choose_spec.choose_spec.choose
    (pbcScalarAdjunction (completedAdicCommProjection X d (n + 1)))
    (pbcScalarAdjunction (completedAdicCommProjection X d n))
    (pbcScalarAdjunction_exists (completedAdicCommProjection X d (n + 1))).exists.choose_spec
    (pbcScalarAdjunction_exists (completedAdicCommProjection X d n)).exists.choose_spec
    (pbcRestrictComp (completedAdicCommProjection X d (n + 1))
      (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))
      (completedAdicCommProjection X d n)
      (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n)))
    (pbcRestrictComp_exists (completedAdicCommProjection X d (n + 1))
      (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))
      (completedAdicCommProjection X d n)
      (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n))).exists.choose_spec N


end AlgebraicGeometry.Scheme
