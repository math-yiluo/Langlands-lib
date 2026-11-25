/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.StandardUnitCocycleOffDiagonal
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.StandardUnitCocycleDiagonal

/-!
# Normalizing unit cocycles on the standard projective-space cover

## References

* Stacks Project, Tag 0BXJ, the double- and triple-overlap calculations
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- A cocycle of units on the standard cover, with at least three homogeneous
coordinates, differs from a standard integer transition cocycle by chart units.
This is a statement about functions, with no module sheaf or gluing conclusion. -/
theorem exists_standardUnitCocycle_normalization (k : Type u) [Field k]
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
      ∀ i j : ULift.{u} (Fin r),
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
            (homOfLE inf_le_left).op (a i).val * (t i j).val =
          (transitionUnit _ (Spec (.of k)) d i j).val *
            (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
              (homOfLE inf_le_right).op (a j).val := by
  obtain ⟨d, a, hoff⟩ := exists_standardUnitCocycle_normalization_offDiagonal k r hr t ht
  have hdiag := standardUnitCocycle_diagonal_normalization k r hr t ht d a hoff
  refine ⟨d, a, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    exact hdiag i
  · exact hoff i j hij

end AlgebraicGeometry.ProjectiveSpace
