import Langlands.BaseChange.RelativeParabolicDiscriminantNorm

/-! # Nonvanishing of the relative parabolic discriminant at a regular norm -/

namespace Langlands.BaseChange

open Langlands.GeneralLinear (BlockShape)
open Langlands.JacquetLanglands (IsRegularSemisimple)

universe u v

section Ordinary

variable {n : ℕ} (B : BlockShape n) (K : Type u) [Field K]

private def blockProjectionMatrix (i : Fin B.length) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal (fun a => if B.coordinateBlock a = i then 1 else 0)

private theorem leviEmbedding_offBlock_eq_zero (m : B.Levi K) (a b : Fin n)
    (hab : B.coordinateBlock a ≠ B.coordinateBlock b) :
    B.leviEmbedding K m a b = 0 := by
  obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective b
  exact B.leviEmbedding_apply_ne K m x y (by simpa [BlockShape.coordinateBlock] using hab)

private theorem blockProjectionMatrix_commute (m : B.Levi K) (i : Fin B.length) :
    Commute (blockProjectionMatrix B K i) (B.leviEmbedding K m).val := by
  show _ * _ = _ * _
  ext a b
  simp only [blockProjectionMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : B.coordinateBlock a = B.coordinateBlock b
  · rw [h, mul_comm]
  · have hz := leviEmbedding_offBlock_eq_zero B K m a b h
    change (B.leviEmbedding K m).val a b = 0 at hz
    rw [hz, mul_zero, zero_mul]

private theorem blockProjectionMatrix_mul_eq_zero {i j : Fin B.length} (h : i ≠ j) :
    blockProjectionMatrix B K i * blockProjectionMatrix B K j = 0 := by
  simp only [blockProjectionMatrix, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext a
  by_cases ha : B.coordinateBlock a = i <;> simp [ha, h]

private theorem blockProjectionMatrix_sandwich_eq_zero {i j : Fin B.length} (h : i ≠ j)
    {X : Matrix (Fin n) (Fin n) K} (hX : X ∈ blockDiagonalLieSubmodule B K) :
    blockProjectionMatrix B K i * X * blockProjectionMatrix B K j = 0 := by
  ext a b
  simp only [blockProjectionMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases ha : B.coordinateBlock a = i <;> by_cases hb : B.coordinateBlock b = j
  · have hab : B.coordinateBlock a ≠ B.coordinateBlock b := by rw [ha, hb]; exact h
    simp [ha, hb, (mem_blockDiagonalLieSubmodule B K X).mp hX a b hab]
  all_goals simp [ha, hb]

private theorem blockDiagonal_of_adjoint_sub_mem {m : B.Levi K}
    (hm : IsRegularSemisimple (B.leviEmbedding K m)) {X : Matrix (Fin n) (Fin n) K}
    (hX : linearAdjoint (B.leviEmbedding K m⁻¹) X - X ∈ blockDiagonalLieSubmodule B K) :
    X ∈ blockDiagonalLieSubmodule B K := by
  rw [mem_blockDiagonalLieSubmodule]
  intro a b hab
  let i := B.coordinateBlock a
  let j := B.coordinateBlock b
  let P := blockProjectionMatrix B K i
  let Q := blockProjectionMatrix B K j
  let G := B.leviEmbedding K m
  let Y := P * X * Q
  have hP : P * G⁻¹.val = G⁻¹.val * P := by
    simpa only [map_inv] using (blockProjectionMatrix_commute B K m⁻¹ i).eq
  have hQ : Q * G.val = G.val * Q := (blockProjectionMatrix_commute B K m j).eq
  have hfix := blockProjectionMatrix_sandwich_eq_zero B K hab hX
  rw [mul_sub, sub_mul, sub_eq_zero, map_inv] at hfix
  change P * (G⁻¹.val * (X * G⁻¹⁻¹.val)) * Q = Y at hfix
  rw [inv_inv] at hfix
  have hYfix : G⁻¹.val * (Y * G.val) = Y := calc
    _ = (G⁻¹.val * P) * X * (Q * G.val) := by simp only [Y, mul_assoc]
    _ = P * (G⁻¹.val * (X * G.val)) * Q := by rw [← hP, hQ]; simp only [mul_assoc]
    _ = Y := hfix
  have hYcomm : Commute Y G.val := by
    show Y * G.val = G.val * Y
    calc
      _ = G.val * (G⁻¹.val * (Y * G.val)) := by
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      _ = _ := by rw [hYfix]
  have hPQ : Q * P = 0 := blockProjectionMatrix_mul_eq_zero B K hab.symm
  have hnil : Y * Y = 0 := calc
    _ = P * X * (Q * P) * X * Q := by simp only [Y, mul_assoc]
    _ = _ := by rw [hPQ]; simp
  let z : GeneralLinear n K :=
    ⟨1 + Y, 1 - Y, by simp [add_mul, mul_sub, hnil], by simp [sub_mul, mul_add, hnil]⟩
  have hz : Commute z G := by
    show z * G = G * z
    exact Units.ext ((Commute.one_left G.val).add_left hYcomm).eq
  obtain ⟨m', hm'⟩ := mem_leviSubgroup_of_commute_regular B hm hz
  have he : z a b = 0 := by rw [← hm']; exact leviEmbedding_offBlock_eq_zero B K m' a b hab
  have hab' : a ≠ b := fun h => hab (congrArg B.coordinateBlock h)
  change ((1 : Matrix (Fin n) (Fin n) K) + Y) a b = 0 at he
  simpa [Y, P, Q, i, j, blockProjectionMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.one_apply_ne hab'] using he

/-- The ordinary relative parabolic discriminant is nonzero on ambient regular
semisimple points of the standard Levi. -/
def RelativeParabolicDiscriminantRegularStatement : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (B : BlockShape n) {m : B.Levi K},
    IsRegularSemisimple (B.leviEmbedding K m) → relativeParabolicDiscriminant B K m ≠ 0

/-- A regular Levi element has no fixed direction in the off-block Lie quotient. -/
theorem relativeParabolicDiscriminant_ne_zero : RelativeParabolicDiscriminantRegularStatement.{u} := by
  intro K _ n B m hm hz
  rw [relativeParabolicDiscriminant, LinearMap.det_eq_zero_iff_ker_ne_bot] at hz
  apply hz
  apply le_antisymm ?_ bot_le
  intro x hx
  change x - relativeParabolicAdjoint B K m⁻¹ x = 0 at hx
  have hfix : relativeParabolicAdjoint B K m⁻¹ x = x := (sub_eq_zero.mp hx).symm
  change x = 0
  revert hfix
  refine Submodule.Quotient.induction_on (blockDiagonalLieSubmodule B K) x ?_
  intro X hfix
  rw [relativeParabolicAdjoint_mk] at hfix
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply blockDiagonal_of_adjoint_sub_mem B K hm
  apply (Submodule.Quotient.mk_eq_zero _).mp
  rw [Submodule.Quotient.mk_sub, hfix, sub_self]

end Ordinary

/-- At an exact regular norm the twisted relative parabolic discriminant is nonzero. -/
theorem twistedRelativeParabolicDiscriminant_ne_zero_of_cyclicNorm
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    {n l : ℕ} (B : BlockShape n) {σ : E ≃ₐ[F] E} (h : IsCyclicAlgebra σ l)
    {δ : B.Levi E} {γ : B.Levi F}
    (hδγ : cyclicNorm σ l (B.leviEmbedding E δ) = baseChange F E n (B.leviEmbedding F γ))
    (hγ : IsRegularSemisimple (B.leviEmbedding F γ)) :
    letI : FiniteDimensional F E := h.1
    twistedRelativeParabolicDiscriminant B σ δ ≠ 0 := by
  rw [twistedRelativeParabolicDiscriminant_eq_of_cyclicNorm B h hδγ]
  exact relativeParabolicDiscriminant_ne_zero B hγ

end Langlands.BaseChange
