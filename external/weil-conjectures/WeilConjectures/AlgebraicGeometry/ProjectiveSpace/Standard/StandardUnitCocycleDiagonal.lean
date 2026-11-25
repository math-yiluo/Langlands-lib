/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits

/-! # Diagonal equations for standard unit cocycles

## References

* Stacks Project, Tag 0BXJ
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- If units `a i` relate a unit cocycle `t` on the standard cover of `ℙ^{r-1}_k` to the
standard transition units of degree `d` off the diagonal, then they also do so on the diagonal. -/
theorem standardUnitCocycle_diagonal_normalization (k : Type u) [Field k]
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
          (homOfLE (le_inf hi hl)).op (t i l).val)
    (d : ℤ)
    (a : ∀ i : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)), standardOpen _ (Spec (.of k)) i)ˣ)
    (hoff : ∀ i j : ULift.{u} (Fin r), i ≠ j →
      (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE inf_le_left).op (a i).val * (t i j).val =
        (transitionUnit _ (Spec (.of k)) d i j).val *
          (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
            (homOfLE inf_le_right).op (a j).val) :
    ∀ i : ULift.{u} (Fin r),
      (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE inf_le_left).op (a i).val * (t i i).val =
        (transitionUnit _ (Spec (.of k)) d i i).val *
          (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
            (homOfLE inf_le_right).op (a i).val := by
  have _hr := hr
  have _hoff := hoff
  intro i
  have ht_diag := ht i i i
    (standardOpen _ (Spec (.of k)) i ⊓ standardOpen _ (Spec (.of k)) i)
    inf_le_left inf_le_left inf_le_left
  have ht_idem : (t i i).val * (t i i).val = (t i i).val := by
    simpa using ht_diag
  have ht_one : (t i i).val = 1 := (t i i).isUnit.mul_eq_left.mp ht_idem
  have hu_diag := transitionUnit_mul_transitionUnit
    (n := ULift.{u} (Fin r)) (S := Spec (.of k)) d i i i
  let U := standardOpen (ULift.{u} (Fin r)) (Spec (.of k)) i
  let ρ := (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
    (homOfLE (inf_le_left : (U ⊓ U) ⊓ U ≤ U ⊓ U)).op
  have hu_val : ρ (transitionUnit _ (Spec (.of k)) d i i).val *
      ρ (transitionUnit _ (Spec (.of k)) d i i).val =
        ρ (transitionUnit _ (Spec (.of k)) d i i).val :=
    congrArg Units.val hu_diag
  have hu_restrict := congrArg (fun x ↦
    (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
      (homOfLE (le_inf le_rfl inf_le_left : U ⊓ U ≤ (U ⊓ U) ⊓ U)).op x) hu_val
  have hu_idem : (transitionUnit _ (Spec (.of k)) d i i).val *
      (transitionUnit _ (Spec (.of k)) d i i).val =
        (transitionUnit _ (Spec (.of k)) d i i).val := by
    dsimp only [ρ] at hu_restrict
    simp only [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      homOfLE_comp, homOfLE_refl, op_id] at hu_restrict
    simpa using hu_restrict
  have hu_one : (transitionUnit _ (Spec (.of k)) d i i).val = 1 :=
    (transitionUnit _ (Spec (.of k)) d i i).isUnit.mul_eq_left.mp hu_idem
  simp only [ht_one, hu_one, mul_one, one_mul]

end AlgebraicGeometry.ProjectiveSpace
