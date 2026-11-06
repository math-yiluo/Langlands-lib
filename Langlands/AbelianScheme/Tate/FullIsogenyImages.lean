import Langlands.AbelianScheme.Tate.FullEvaluationKernel

/-! # Full Tate images of reverse multiplication factorizations -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} {G H : Grp (Over S)}
  [IsCommMonObj G.X] [IsCommMonObj H.X] (T : Over S)

/-- Multiplication of the group scheme acts as natural multiplication on its Tate group. -/
theorem map_multiplication_apply (P : ℕ → Prop) (n : ℕ) (x : Integral G T P) :
    map T P (multiplication G (n : ℤ)) x = n • x := by
  apply Subtype.ext
  funext i
  apply toSection_injective G T i.val
  change (Additive.toMul (x.val i)).val ≫ (multiplication G (n : ℤ)).hom.hom =
    ((Additive.toMul (x.val i)).val) ^ n
  rw [points_multiplication, zpow_natCast]

variable (n : Index (fun _ => True)) (f : G ⟶ H) (r : H ⟶ G)
  (hfr : f ≫ r = multiplication G (n.val : ℤ))
  (hrf : r ≫ f = multiplication H (n.val : ℤ))

include hfr in
theorem map_reverse_comp (x : Full G T) :
    map T (fun _ => True) r (map T (fun _ => True) f x) = n.val • x := by
  change (map T (fun _ => True) r).comp (map T (fun _ => True) f) x = _
  rw [← map_comp, hfr, map_multiplication_apply]

include hrf in
theorem map_comp_reverse (y : Full H T) :
    map T (fun _ => True) f (map T (fun _ => True) r y) = n.val • y := by
  change (map T (fun _ => True) f).comp (map T (fun _ => True) r) y = _
  rw [← map_comp, hrf, map_multiplication_apply]

/-- The reverse map identifies the full Tate group with the kernel of evaluation after f. -/
def fullReverseKernelEquiv :
    Full H T ≃+ ((evaluation H T (fun _ => True) n).comp
      (map T (fun _ => True) f)).ker :=
  AddEquiv.ofBijective
    ({ toFun := fun y => ⟨map T (fun _ => True) r y, by
         change evaluation H T (fun _ => True) n
           (map T (fun _ => True) f (map T (fun _ => True) r y)) = 0
         rw [map_comp_reverse T n f r hrf, map_nsmul]
         exact level_nsmul_eq_zero H T n.val _⟩
       map_zero' := by apply Subtype.ext; exact map_zero _
       map_add' := by intros; apply Subtype.ext; exact map_add _ _ _ } :
      Full H T →+ ((evaluation H T (fun _ => True) n).comp
        (map T (fun _ => True) f)).ker)
    ⟨by
      intro y z hyz
      apply sub_eq_zero.mp
      apply full_eq_zero_of_nsmul_eq_zero H T n.property.1
      rw [smul_sub, sub_eq_zero]
      have h := congrArg (fun x : Full G T => map T (fun _ => True) f x)
        (congrArg Subtype.val hyz)
      change map T (fun _ => True) f (map T (fun _ => True) r y) =
        map T (fun _ => True) f (map T (fun _ => True) r z) at h
      simpa only [map_comp_reverse T n f r hrf] using h,
     by
      intro x
      obtain ⟨y, hy⟩ := full_exists_nsmul_of_evaluation_eq_zero H T n
        (map T (fun _ => True) f x.val) x.property
      refine ⟨y, Subtype.ext ?_⟩
      apply sub_eq_zero.mp
      apply full_eq_zero_of_nsmul_eq_zero G T n.property.1
      rw [smul_sub, sub_eq_zero]
      calc
        n.val • map T (fun _ => True) r y =
            map T (fun _ => True) r (n.val • y) := (map_nsmul _ _ _).symm
        _ = map T (fun _ => True) r (map T (fun _ => True) f x.val) :=
          congrArg (map T (fun _ => True) r) hy
        _ = n.val • x.val := map_reverse_comp T n f r hfr x.val⟩

include hfr hrf in
@[simp]
theorem fullReverseKernelEquiv_apply_val (y : Full H T) :
    (fullReverseKernelEquiv T n f r hfr hrf y).val = map T (fun _ => True) r y := rfl

include hfr hrf in
/-- An exact image criterion involving only one torsion coordinate. -/
theorem exists_map_reverse_iff (x : Full G T) :
    (∃ y : Full H T, map T (fun _ => True) r y = x) ↔
      levelMap T f n.val (evaluation G T (fun _ => True) n x) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (fullReverseKernelEquiv T n f r hfr hrf y).property
  · intro hx
    obtain ⟨y, hy⟩ := (fullReverseKernelEquiv T n f r hfr hrf).surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

end Langlands.GroupScheme.Tate
