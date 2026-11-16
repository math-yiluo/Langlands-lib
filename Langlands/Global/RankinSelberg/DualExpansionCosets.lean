import Langlands.Global.RankinSelberg.DualExpansionData

/-! # The surviving cosets of the column orthogonality -/

noncomputable section
universe u
open NumberField
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (sqZeroUnit sqZeroUnit_val)

variable (F : Type u) [Field F] [NumberField F] {m K : ℕ}

/-- The rational row element `1 + rowMat β` of `GL_(m+K+1)(F)`. -/
def rowRat (β : Fin m → F) : RationalGL F (m + K + 1) :=
  sqZeroUnit (rowMat m K β) (rowMat_mul_rowMat β β)

omit [NumberField F] in
theorem rowRat_mul (β β' : Fin m → F) :
    rowRat F (K := K) β * rowRat F β' = rowRat F (β + β') := by
  apply Units.ext
  simp only [rowRat, Units.val_mul, sqZeroUnit_val]
  rw [add_mul, one_mul, mul_add, mul_one, rowMat_mul_rowMat, add_zero, rowMat_add]
  abel

omit [NumberField F] in
theorem rowRat_zero : rowRat F (m := m) (K := K) 0 = 1 := by
  apply Units.ext
  simp only [rowRat, sqZeroUnit_val, rowMat_zero, add_zero, Units.val_one]

/-- The last row of `g` has `1` at the last place and `0` at the places `m, …, m+K-1`. -/
def SurvivorRow (g : RationalGL F (m + K + 1)) : Prop :=
  ∀ i : Fin (K + 1), (g : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) (Fin.last (m + K))
    ⟨m + i, by omega⟩ = if (i : ℕ) = K then 1 else 0

omit [NumberField F] in
theorem lastRow_padGL_mul_rowRat (a : RationalGL F (m + K)) (β : Fin m → F)
    (b : Fin (m + K + 1)) :
    ((padGL (Nat.le_succ (m + K)) a * rowRat F β : RationalGL F (m + K + 1)) :
        Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) (Fin.last (m + K)) b =
      (if hb : (b : ℕ) < m then β ⟨b, hb⟩ else 0) + (if Fin.last (m + K) = b then 1 else 0) := by
  rw [Units.val_mul, rowRat, sqZeroUnit_val, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single (Fin.last (m + K))]
  · simp only [padGL_apply, Fin.val_last, lt_irrefl, dite_false, ite_true, one_mul, rowMat]
    rw [add_comm]
  · intro l _ hl
    simp only [padGL_apply, Fin.val_last, lt_irrefl, dite_false, Ne.symm hl, ite_false, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `N(F) (diag(a, 1) ξ_β)`, the coset attached to `(N(F) a, β)`. -/
def survivorMap (p : UnipotentRationalCosets F (m + K) × (Fin m → F)) :
    UnipotentRationalCosets F (m + K + 1) :=
  Quotient.mk _ (padGL (Nat.le_succ (m + K)) p.1.out * rowRat F p.2)

theorem survivorRow_of_rightRel {g h : RationalGL F (m + K + 1)}
    (hgh : QuotientGroup.rightRel (rationalUpperUnipotent F (m + K + 1)) g h)
    (hg : SurvivorRow F g) : SurvivorRow F h := by
  have hn := (mem_rationalUpperUnipotent_iff F _).mp (QuotientGroup.rightRel_apply.mp hgh)
  have : h = (h * g⁻¹) * g := by group
  intro i
  rw [this, Units.val_mul, lastRow_unitriangular_mul hn]
  exact hg i

theorem survivorRow_out_survivorMap (p : UnipotentRationalCosets F (m + K) × (Fin m → F)) :
    SurvivorRow F (survivorMap F p).out := by
  refine survivorRow_of_rightRel F (Quotient.exact (Quotient.out_eq _).symm) ?_
  intro i
  rw [lastRow_padGL_mul_rowRat]
  simp only [Fin.ext_iff, Fin.val_last]
  rw [dite_eq_right (by omega)]
  by_cases hi : (i : ℕ) = K
  · rw [ite_eq_left (by omega), ite_eq_left hi, zero_add]
  · rw [ite_eq_right (by omega), ite_eq_right hi, zero_add]

theorem rightRel_padGL_mul_of_rightRel {a b : RationalGL F (m + K)}
    (hab : QuotientGroup.rightRel (rationalUpperUnipotent F (m + K)) a b) (β : Fin m → F) :
    QuotientGroup.rightRel (rationalUpperUnipotent F (m + K + 1))
      (padGL (Nat.le_succ (m + K)) a * rowRat F β) (padGL (Nat.le_succ (m + K)) b * rowRat F β) := by
  rw [QuotientGroup.rightRel_apply] at hab ⊢
  have : padGL (Nat.le_succ (m + K)) b * rowRat F β * (padGL (Nat.le_succ (m + K)) a * rowRat F β)⁻¹ =
      padGL (Nat.le_succ (m + K)) (b * a⁻¹) := by
    rw [map_mul, map_inv]
    group
  rw [this, mem_rationalUpperUnipotent_iff]
  exact isUnitriangular_padGL _ _ ((mem_rationalUpperUnipotent_iff F _).mp hab)

/-- Every surviving coset is in the image of `survivorMap`. -/
theorem exists_survivorMap_eq (q : UnipotentRationalCosets F (m + K + 1))
    (hq : SurvivorRow F q.out) : ∃ p, survivorMap F p = q := by
  set g := q.out with hgdef
  let β₀ : Fin m → F := fun j => (g : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F)
    (Fin.last (m + K)) ⟨j, by omega⟩
  set g₁ := g * rowRat F (-β₀) with hg₁
  have hrow : ∀ b, (g₁ : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) (Fin.last (m + K)) b =
      (1 : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) (Fin.last (m + K)) b := by
    intro b
    rw [hg₁, Units.val_mul, rowRat, sqZeroUnit_val, mul_add, mul_one, Matrix.add_apply,
      Matrix.mul_apply, Finset.sum_eq_single (Fin.last (m + K))]
    · have hlast := hq (Fin.last K)
      simp only [Fin.val_last, ite_true] at hlast
      have hl : (g : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) (Fin.last (m + K))
          (Fin.last (m + K)) = 1 := by
        convert hlast using 2
        exact Fin.ext (by simp)
      rw [hl, one_mul]
      simp only [rowMat, Fin.val_last, ite_true, Pi.neg_apply]
      by_cases hb : (b : ℕ) < m
      · rw [dite_eq_left hb, Matrix.one_apply_ne (fun h => by
          have := congrArg Fin.val h; simp at this; omega)]
        simp [β₀]
      · rw [dite_eq_right hb, add_zero]
        by_cases hbl : (b : ℕ) = m + K
        · have : b = Fin.last (m + K) := Fin.ext hbl
          subst this
          rw [hl, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne (fun h => by
            have := congrArg Fin.val h; simp at this; omega)]
          have hi := hq ⟨(b : ℕ) - m, by omega⟩
          simp only at hi
          rw [ite_eq_right (by omega)] at hi
          convert hi using 2
          ext; simp; omega
    · intro l _ hl
      have : ¬((l : ℕ) = m + K) := fun h => hl (Fin.ext (by simpa using h))
      simp only [rowMat, this, ite_false, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  obtain ⟨g', n, hn, hprod⟩ := exists_unitriangular_mul_padGL g₁ hrow
  refine ⟨(Quotient.mk _ g', β₀), ?_⟩
  conv_rhs => rw [← Quotient.out_eq q]
  apply Quotient.sound
  have hg : g = g₁ * rowRat F β₀ := by
    rw [hg₁, mul_assoc, rowRat_mul, neg_add_cancel, rowRat_zero, mul_one]
  have h1 : QuotientGroup.rightRel (rationalUpperUnipotent F (m + K + 1))
      (padGL (Nat.le_succ (m + K)) g' * rowRat F β₀) g := by
    rw [QuotientGroup.rightRel_apply, hg]
    have : g₁ * rowRat F β₀ * (padGL (Nat.le_succ (m + K)) g' * rowRat F β₀)⁻¹ =
        g₁ * (padGL (Nat.le_succ (m + K)) g')⁻¹ := by group
    rw [this]
    have : (g₁ * (padGL (Nat.le_succ (m + K)) g')⁻¹ : RationalGL F (m + K + 1)) =
        unitriangularUnit n hn := by
      apply Units.ext
      rw [Units.val_mul, ← hprod, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_one]
      rfl
    rw [this, mem_rationalUpperUnipotent_iff]
    exact hn
  have h2 : QuotientGroup.rightRel (rationalUpperUnipotent F (m + K + 1))
      (padGL (Nat.le_succ (m + K)) (Quotient.mk _ g' : UnipotentRationalCosets F (m + K)).out *
        rowRat F β₀) (padGL (Nat.le_succ (m + K)) g' * rowRat F β₀) :=
    rightRel_padGL_mul_of_rightRel F (Quotient.exact (Quotient.out_eq _)) β₀
  exact (QuotientGroup.rightRel _).iseqv.trans h2 h1

/-- `survivorMap` is injective. -/
theorem survivorMap_injective : Function.Injective (survivorMap F (m := m) (K := K)) := by
  rintro ⟨q₁, β₁⟩ ⟨q₂, β₂⟩ h
  have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
  have hn := (mem_rationalUpperUnipotent_iff F _).mp hr
  have hrow : ∀ b, ((padGL (Nat.le_succ (m + K)) q₂.out * rowRat F β₂ : RationalGL F (m + K + 1)) :
      Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) (Fin.last (m + K)) b =
      ((padGL (Nat.le_succ (m + K)) q₁.out * rowRat F β₁ : RationalGL F (m + K + 1)) :
        Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) (Fin.last (m + K)) b := by
    intro b
    have heq : padGL (Nat.le_succ (m + K)) q₂.out * rowRat F β₂ =
        (padGL (Nat.le_succ (m + K)) q₂.out * rowRat F β₂ *
          (padGL (Nat.le_succ (m + K)) q₁.out * rowRat F β₁)⁻¹) *
          (padGL (Nat.le_succ (m + K)) q₁.out * rowRat F β₁) := by group
    rw [heq, Units.val_mul, lastRow_unitriangular_mul hn]
  have hβ : β₁ = β₂ := by
    funext j
    have := hrow ⟨j, by omega⟩
    rw [lastRow_padGL_mul_rowRat, lastRow_padGL_mul_rowRat, dite_eq_left j.isLt,
      dite_eq_left j.isLt] at this
    have hne : Fin.last (m + K) ≠ ⟨j, by omega⟩ := fun h' => by
      have := congrArg Fin.val h'; simp at this; omega
    rw [ite_eq_right hne] at this
    simp only [add_zero, Fin.eta] at this
    exact this.symm
  subst hβ
  have hpad : padGL (Nat.le_succ (m + K)) q₂.out * rowRat F β₁ *
      (padGL (Nat.le_succ (m + K)) q₁.out * rowRat F β₁)⁻¹ =
        padGL (Nat.le_succ (m + K)) (q₂.out * q₁.out⁻¹) := by
    rw [map_mul, map_inv]
    group
  rw [hpad] at hn
  have hu : PrimitiveAdelicHeight.IsUnitriangular
      ((q₂.out * q₁.out⁻¹ : RationalGL F (m + K)) : Matrix (Fin (m + K)) (Fin (m + K)) F) := by
    refine ⟨fun c d hcd => ?_, fun c => ?_⟩
    · have := hn.1 (show (Fin.castSucc d : Fin (m + K + 1)) < Fin.castSucc c from hcd)
      rw [padGL_apply, dite_eq_left (by simp), dite_eq_left (by simp)] at this
      exact this
    · have := hn.2 (Fin.castSucc c)
      rw [padGL_apply, dite_eq_left (by simp), dite_eq_left (by simp)] at this
      exact this
  refine Prod.ext ?_ rfl
  rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr ((mem_rationalUpperUnipotent_iff F _).mpr hu)

end Langlands.Global.RankinSelbergGlobal.Unfolding
