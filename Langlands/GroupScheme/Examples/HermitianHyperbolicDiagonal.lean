import Langlands.GroupScheme.Examples.SU3RootParameters
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Diagonal tori on several hyperbolic planes -/

noncomputable section

universe u v w z

namespace Langlands.GroupScheme.HermitianRoot.MultiHyperbolic

open SU3Root

/-- Two endpoint families separated by the remaining coordinates. -/
abbrev Index (α : Type v) (β : Type w) := α ⊕ (β ⊕ α)

variable {A : Type u} {B : Type z} [CommRing A] [CommRing B]
  {α : Type v} {β : Type w} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The full Gram matrix with identity hyperbolic cross blocks. -/
def gram (M : Matrix β β A) : Matrix (Index α β) (Index α β) A
  | Sum.inl i, Sum.inr (Sum.inr j) => if i = j then 1 else 0
  | Sum.inr (Sum.inr i), Sum.inl j => if i = j then 1 else 0
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => M i j
  | _, _ => 0

/-- The diagonal weights are `t`, identity, and `t⁻¹`. -/
def weights : (α → Aˣ) →* (Index α β → Aˣ) where
  toFun t := Sum.elim t (Sum.elim (fun _ => 1) (fun i => (t i)⁻¹))
  map_one' := by
    funext i
    rcases i with i | i | i <;> simp
  map_mul' t s := by
    funext i
    rcases i with i | i | i <;> simp [mul_comm]

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
@[simp] theorem weights_top (t : α → Aˣ) (i : α) :
    weights (β := β) t (Sum.inl i) = t i := rfl

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
@[simp] theorem weights_middle (t : α → Aˣ) (i : β) :
    weights t (Sum.inr (Sum.inl i)) = 1 := rfl

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
@[simp] theorem weights_bottom (t : α → Aˣ) (i : α) :
    weights (β := β) t (Sum.inr (Sum.inr i)) = (t i)⁻¹ := rfl

/-- The actual diagonal invertible matrices, as a group homomorphism. -/
def diagonal : (α → Aˣ) →* Matrix.GeneralLinearGroup (Index α β) A where
  toFun t :=
    { val := Matrix.diagonal fun i => (weights t i : A)
      inv := Matrix.diagonal fun i => ((weights t i)⁻¹ : Aˣ)
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal]
        simp
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal]
        simp }
  map_one' := by
    apply Units.ext
    simp
  map_mul' t s := by
    apply Units.ext
    simp only [Units.val_mul, Matrix.diagonal_mul_diagonal, map_mul, Pi.mul_apply,
      Units.val_mul]

@[simp] theorem diagonal_val (t : α → Aˣ) :
    (diagonal (β := β) t : Matrix (Index α β) (Index α β) A) =
      Matrix.diagonal fun i => (weights t i : A) := rfl

/-- Each endpoint parameter is recovered from its diagonal matrix entry. -/
theorem diagonal_injective : Function.Injective (diagonal (A := A) (α := α) (β := β)) := by
  intro t s h
  funext i
  apply Units.ext
  simpa only [diagonal_val, Matrix.diagonal_apply_eq, weights_top] using
    congrArg (fun g : Matrix.GeneralLinearGroup (Index α β) A => g (Sum.inl i) (Sum.inl i)) h

/-- The products of the positive and negative endpoint weights cancel. -/
@[simp] theorem det_diagonal (t : α → Aˣ) :
    Matrix.GeneralLinearGroup.det (diagonal (β := β) t) = 1 := by
  apply Units.ext
  change (Matrix.diagonal (fun i : Index α β => (weights t i : A))).det = 1
  rw [Matrix.det_diagonal]
  simp only [Index, Fintype.prod_sum_type, weights_top, weights_middle, weights_bottom,
    Units.val_one, Finset.prod_const_one, one_mul]
  rw [← Finset.prod_mul_distrib]
  simp

/-- The diagonal construction commutes with every coefficient homomorphism. -/
theorem diagonal_map (f : A →+* B) (t : α → Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagonal (β := β) t) =
      diagonal (fun i => Units.map f.toMonoidHom (t i)) := by
  apply Units.ext
  change (Matrix.diagonal (fun i : Index α β => (weights t i : A))).map f = _
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  rcases i with i | i | i <;> simp [weights]

/-- Fixed ground scalars give full-pairing isometries, without any condition
on the remaining Gram block. -/
theorem diagonal_preserves (c : RingInvolution A) (M : Matrix β β A)
    (t : α → Aˣ) (ht : ∀ i, c.bar (t i : A) = (t i : A)) :
    ((diagonal (β := β) t : Matrix (Index α β) (Index α β) A).map c.bar).transpose *
      gram M * (diagonal (β := β) t : Matrix (Index α β) (Index α β) A) = gram M := by
  have hi : ∀ i, c.bar ((t i)⁻¹ : Aˣ) = ((t i)⁻¹ : Aˣ) := by
    intro i
    have hb : c.bar ((t i)⁻¹ : Aˣ) * (t i : A) = 1 := by
      rw [← ht i, ← map_mul]
      simp
    calc
      c.bar ((t i)⁻¹ : Aˣ) = c.bar ((t i)⁻¹ : Aˣ) * ((t i : A) * ((t i)⁻¹ : Aˣ)) := by simp
      _ = (t i)⁻¹ := by rw [← mul_assoc, hb, one_mul]
  simp only [diagonal_val, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [gram, weights, ht, hi, mul_ite, ite_mul]
  all_goals split_ifs with hij <;> simp_all

end Langlands.GroupScheme.HermitianRoot.MultiHyperbolic
