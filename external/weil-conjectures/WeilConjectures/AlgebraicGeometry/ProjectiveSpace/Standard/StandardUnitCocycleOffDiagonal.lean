/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SixFunctors.PairwiseLaurentUnitExpansion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SixFunctors.PairwiseCocycleNormalization

/-! # Off-diagonal normalization of standard unit cocycles

## References

* Stacks Project, Tag 0BXJ
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- A unit cocycle `t` on the standard cover of `ℙ^{r-1}_k`, `r ≥ 3`, is, off the diagonal,
cohomologous to the standard transition units of some degree `d`, via units `a i` on the charts. -/
theorem exists_standardUnitCocycle_normalization_offDiagonal (k : Type u) [Field k]
    (r : ℕ) (hr : 3 ≤ r)
    (t : ∀ i j : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
        standardOpen _ (Spec (.of k)) i ⊓ standardOpen _ (Spec (.of k)) j)ˣ)
    (ht : ∀ (i j l : ULift.{u} (Fin r))
      (W : ℙ(ULift.{u} (Fin r); Spec (.of k)).Opens)
      (hi : W ≤ standardOpen _ (Spec (.of k)) i)
      (hj : W ≤ standardOpen _ (Spec (.of k)) j)
      (hl : W ≤ standardOpen _ (Spec (.of k)) l),
      (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hi hj)).op (t i j).val *
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hj hl)).op (t j l).val =
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hi hl)).op (t i l).val) :
    ∃ d : ℤ, ∃ a : ∀ i : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)), standardOpen _ (Spec (.of k)) i)ˣ,
      ∀ i j : ULift.{u} (Fin r), i ≠ j →
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
            (homOfLE inf_le_left).op (a i).val * (t i j).val =
          (transitionUnit _ (Spec (.of k)) d i j).val *
            (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
              (homOfLE inf_le_right).op (a j).val := by
  obtain ⟨e, c, hpair⟩ := exists_pairwise_laurent_unit_expansion k r hr t
  exact exists_standardUnitCocycle_normalization_of_pairwise_laurent
    k r hr t ht e c hpair

end AlgebraicGeometry.ProjectiveSpace
