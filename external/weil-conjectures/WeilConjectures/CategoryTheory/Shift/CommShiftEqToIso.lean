/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Transport of shift structures along equalities of functors

If `h : F = G` is an equality of functors and `G` commutes with shifts, then transporting the
shift structure of `G` to `F` along `h` makes `eqToIso h` commute with shifts
(`CategoryTheory.NatTrans.CommShift.eqToIso_hom`).
-/

@[expose] public section

namespace CategoryTheory.NatTrans.CommShift

/-- An equality of functors transports a shift structure so that its identity comparison
commutes with shifts. -/
theorem eqToIso_hom {A B : Type*} [Category* A] [Category* B] [HasShift A ℤ] [HasShift B ℤ]
    {F G : A ⥤ B} (h : F = G) (q : G.CommShift ℤ) :
    @NatTrans.CommShift _ _ _ _ _ _ (eqToIso h).hom ℤ _ _ _
      (cast (congrArg (fun H : A ⥤ B ↦ H.CommShift ℤ) h.symm) q) q := by
  cases h
  constructor
  intro n
  ext K
  simp

end CategoryTheory.NatTrans.CommShift
