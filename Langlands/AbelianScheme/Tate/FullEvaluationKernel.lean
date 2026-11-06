import Langlands.AbelianScheme.Tate.FullSeparation

/-! # The kernel of a full Tate evaluation -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- A full coherent family with zero n-coordinate admits division by n. -/
theorem full_exists_nsmul_of_evaluation_eq_zero
    (n : Index (fun _ => True)) (x : Full G T)
    (hx : evaluation G T (fun _ => True) n x = 0) :
    ∃ y : Full G T, n.val • y = x := by
  let j : Index (fun _ => True) → Index (fun _ => True) :=
    fun i => ⟨n.val * i.val, Nat.mul_pos n.property.1 i.property.1, trivial⟩
  have hmem (i : Index (fun _ => True)) :
      (Additive.toMul (x.val (j i))).val ∈ levelGroup G T i.val := by
    have hi := evaluation_transition G T (fun _ => True) n (j i)
      (dvd_mul_right n.val i.val) x
    rw [hx] at hi
    have hi' := congrArg (toSection G T n.val) hi
    rw [toSection_transition, map_zero] at hi'
    change ((n.val * i.val) / n.val) • toSection G T (n.val * i.val) (x.val (j i)) = 0 at hi'
    rw [Nat.mul_div_cancel_left _ n.property.1] at hi'
    exact (mem_levelGroup G T i.val _).mpr hi'
  let y : Full G T := ⟨fun i => Additive.ofMul ⟨(Additive.toMul (x.val (j i))).val, hmem i⟩, by
    intro i k hik
    apply toSection_injective G T i.val
    have hc := congrArg (toSection G T (j i).val)
      (x.property (j i) (j k) (Nat.mul_dvd_mul_left n.val hik))
    rw [toSection_transition] at hc
    change ((n.val * k.val) / (n.val * i.val)) •
      toSection G T (j k).val (x.val (j k)) =
        toSection G T (j i).val (x.val (j i)) at hc
    rw [Nat.mul_div_mul_left _ _ n.property.1] at hc
    exact hc⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  funext i
  apply toSection_injective G T i.val
  have hc := congrArg (toSection G T i.val)
    (x.property i (j i) (dvd_mul_left i.val n.val))
  rw [toSection_transition] at hc
  change ((n.val * i.val) / i.val) • toSection G T (j i).val (x.val (j i)) =
    toSection G T i.val (x.val i) at hc
  rw [Nat.mul_div_cancel _ i.property.1] at hc
  exact hc

/-- A family has zero n-coordinate exactly when it is n times a full family. -/
theorem full_evaluation_eq_zero_iff
    (n : Index (fun _ => True)) (x : Full G T) :
    evaluation G T (fun _ => True) n x = 0 ↔ ∃ y : Full G T, n.val • y = x := by
  constructor
  · exact full_exists_nsmul_of_evaluation_eq_zero G T n x
  · rintro ⟨y, rfl⟩
    rw [map_nsmul]
    exact level_nsmul_eq_zero G T n.val _

/-- Multiplication by n identifies the full Tate group with the evaluation kernel. -/
def fullEvaluationKernelEquiv (n : Index (fun _ => True)) :
    Full G T ≃+ (evaluation G T (fun _ => True) n).ker :=
  AddEquiv.ofBijective
    ({ toFun := fun y => ⟨n.val • y, (full_evaluation_eq_zero_iff G T n _).mpr ⟨y, rfl⟩⟩
       map_zero' := by apply Subtype.ext; exact nsmul_zero _
       map_add' := by intros; apply Subtype.ext; exact nsmul_add _ _ _ } :
        Full G T →+ (evaluation G T (fun _ => True) n).ker)
    ⟨by
      intro x y h
      apply sub_eq_zero.mp
      apply full_eq_zero_of_nsmul_eq_zero G T n.property.1
      rw [smul_sub, sub_eq_zero]
      exact congrArg Subtype.val h,
     by
      intro x
      obtain ⟨y, hy⟩ := full_exists_nsmul_of_evaluation_eq_zero G T n x.val x.property
      exact ⟨y, Subtype.ext hy⟩⟩

@[simp]
theorem fullEvaluationKernelEquiv_apply_val (n : Index (fun _ => True)) (x : Full G T) :
    (fullEvaluationKernelEquiv G T n x).val = n.val • x := rfl

end Langlands.GroupScheme.Tate
