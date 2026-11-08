import Langlands.GroupScheme.Examples.HermitianRootLeviReflections

/-! # Action of Hermitian middle reflections -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

variable {L : Type u} {ι : Type v}
  [Field L] [Fintype ι] {c : RingInvolution L}

namespace DiagonalForm

/-- Vanishing of the self-pairing forces the vector to be zero. -/
def IsAnisotropic (H : DiagonalForm c ι) : Prop :=
  ∀ x : ι → L, H.pairing x x = 0 → x = 0

theorem pairing_sub_left (H : DiagonalForm c ι) (x y z : ι → L) :
    H.pairing (x - y) z = H.pairing x z - H.pairing y z := by
  simp only [sub_eq_add_neg, pairing_add_left, pairing_neg_left]

theorem pairing_sub_right (H : DiagonalForm c ι) (x y z : ι → L) :
    H.pairing x (y - z) = H.pairing x y - H.pairing x z := by
  simp only [sub_eq_add_neg, pairing_add_right, pairing_neg_right]

theorem pairing_conjugate_self (H : DiagonalForm c ι) (x : ι → L) :
    H.pairing (fun i => c.bar (x i)) (fun i => c.bar (x i)) =
      H.pairing x x := by
  simp only [pairing, RingInvolution.bar_bar]
  apply Finset.sum_congr rfl
  intro i _
  ring

end DiagonalForm

variable {H : DiagonalForm c ι}

namespace Parameters

/-- The reflection parameter obtained from two equal-norm vectors. -/
def betweenParameter (w v : ι → L) (heq : H.pairing w w = H.pairing v v) :
    Parameters H :=
  ⟨(fun i => c.bar ((w - v) i), H.pairing w (w - v)), by
    rw [DiagonalForm.pairing_conjugate_self, DiagonalForm.bar_pairing]
    simp only [DiagonalForm.pairing_sub_left, DiagonalForm.pairing_sub_right]
    linear_combination heq⟩

@[simp] theorem betweenParameter_vector (w v : ι → L)
    (heq : H.pairing w w = H.pairing v v) :
    (betweenParameter w v heq).vector = fun i => c.bar ((w - v) i) := rfl

@[simp] theorem betweenParameter_scalar (w v : ι → L)
    (heq : H.pairing w w = H.pairing v v) :
    (betweenParameter w v heq).scalar = H.pairing w (w - v) := rfl

theorem betweenParameter_scalar_ne_zero (hH : H.IsAnisotropic)
    (w v : ι → L) (heq : H.pairing w w = H.pairing v v) (hne : w ≠ v) :
    (betweenParameter w v heq).scalar ≠ 0 := by
  intro hz
  have hq := (betweenParameter w v heq).equation
  rw [hz, map_zero, zero_add, betweenParameter_vector,
    DiagonalForm.pairing_conjugate_self] at hq
  exact hne (sub_eq_zero.mp (hH (w - v) hq.symm))

end Parameters

variable [DecidableEq ι]

theorem reflectionMiddle_mulVec (x : Parameters H) (w : ι → L) :
    (reflectionMiddle x).mulVec w = fun i =>
      w i - c.bar (x.vector i) *
        H.pairing w (fun j => c.bar (x.vector j)) / x.scalar := by
  rw [reflectionMiddle, Matrix.sub_mulVec, Matrix.one_mulVec]
  funext i
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    DiagonalForm.pairing, RingInvolution.bar_bar]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem reflectionMiddle_between_mulVec (w v : ι → L)
    (heq : H.pairing w w = H.pairing v v)
    (hne : (Parameters.betweenParameter w v heq).scalar ≠ 0) :
    (reflectionMiddle (Parameters.betweenParameter w v heq)).mulVec w = v := by
  rw [reflectionMiddle_mulVec]
  funext i
  simp only [Parameters.betweenParameter_vector, Parameters.betweenParameter_scalar,
    RingInvolution.bar_bar, Pi.sub_apply]
  change w i - (w i - v i) * H.pairing w (w - v) / H.pairing w (w - v) = v i
  rw [mul_div_cancel_right₀ _ (show H.pairing w (w - v) ≠ 0 from hne)]
  ring

theorem reflectionMiddle_between_fixes (w v : ι → L)
    (heq : H.pairing w w = H.pairing v v) (t : ι → L)
    (ht : H.pairing t (w - v) = 0) :
    (reflectionMiddle (Parameters.betweenParameter w v heq)).mulVec t = t := by
  rw [reflectionMiddle_mulVec]
  funext i
  simp only [Parameters.betweenParameter_vector, RingInvolution.bar_bar, ht,
    mul_zero, zero_div, sub_zero]

/-- Equal-norm vectors can be matched by an actual elementary Levi element,
while all vectors orthogonal to their difference remain fixed. -/
theorem exists_elementary_levi_between (hH : H.IsAnisotropic)
    (s : L) (hs : s + c.bar s = 0) (hsne : s ≠ 0)
    (w v : ι → L) (heq : H.pairing w w = H.pairing v v) :
    ∃ g ∈ elementarySubgroup H, ∃ (a : L) (T : Matrix ι ι L),
      a ≠ 0 ∧ (g : Matrix (Index ι) (Index ι) L) = leviMatrix (c := c) a T ∧
        T.mulVec w = v ∧
        ∀ t : ι → L, H.pairing t (w - v) = 0 → T.mulVec t = t := by
  by_cases hwv : w = v
  · refine ⟨1, (elementarySubgroup H).one_mem, 1, 1, one_ne_zero, ?_, ?_, ?_⟩
    · change (1 : Matrix (Index ι) (Index ι) L) = leviMatrix (c := c) 1 1
      ext i j
      rcases i with i | i | i <;> rcases j with j | j | j <;>
        simp [leviMatrix, Matrix.fromBlocks, Matrix.one_apply]
    · simpa only [Matrix.one_mulVec] using hwv
    · intro t _
      exact Matrix.one_mulVec t
  · let x := Parameters.betweenParameter w v heq
    have hx : x.scalar ≠ 0 := Parameters.betweenParameter_scalar_ne_zero hH w v heq hwv
    refine ⟨reflectionLeviElement x hx s hs hsne,
      reflectionLeviElement_mem_elementarySubgroup x hx s hs hsne,
      x.scalar / s, reflectionMiddle x, div_ne_zero hx hsne,
      reflectionLeviElement_val x hx s hs hsne,
      reflectionMiddle_between_mulVec w v heq hx, ?_⟩
    intro t ht
    exact reflectionMiddle_between_fixes w v heq t ht

end Langlands.GroupScheme.HermitianRoot
