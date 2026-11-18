import Langlands.Representation.Archimedean.RealRationalCompactFamilies
import Langlands.Representation.Archimedean.RealGenericMultiplierDegeneration

/-! # Explicit specialization of cleared finite compact multiplier families -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealClearedCompactDegeneration

open MvPolynomial RealBlockMultiplier RealGenericMultiplierDegeneration
  RealRationalCompactFamilies RealSignedTailPolynomial Finset

def pole (ε : ℤ) (r : ℕ) : ℂ := -((ε : ℂ) + 2 * r + 1)

def poleComplement (ε : ℤ) (B r : ℕ) : ℂ :=
  ∏ i ∈ (range B).erase r, ((ε : ℂ) + 2 * i + 1 + pole ε r)

theorem poleComplement_ne_zero (ε : ℤ) (B r : ℕ) : poleComplement ε B r ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro i hi
  exact genericSeq_denom_at_pole_ne_zero ε (mem_erase.mp hi).1

theorem clearedSeq_at_pole {σ : Type*} (ε : ℤ) {B r m : ℕ}
    (hr : r < B) (hm : m ≤ B) (q : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hq : eval z q = pole ε r) :
    eval z (clearedSeq ε B m q) =
      poleComplement ε B r * regularizedSeq (pole ε r) ε r m := by
  simp only [clearedSeq, map_mul, map_prod, map_sub, map_add, eval_C, hq]
  by_cases hmr : m ≤ r
  · have hz : (∏ i ∈ Ico m B, ((ε : ℂ) + 2 * i + 1 + pole ε r)) = 0 := by
      apply prod_eq_zero (mem_Ico.mpr ⟨hmr, hr⟩)
      unfold pole
      ring
    rw [hz, mul_zero]
    have hzero : regularizedSeq (pole ε r) ε r m = 0 :=
      regularizedSeq_at_pole_eq_zero ε hmr
    rw [hzero, mul_zero]
  · have hrm : r < m := by omega
    let a : ℕ → ℂ := fun i => (ε : ℂ) + 2 * i + 1 - pole ε r
    let d : ℕ → ℂ := fun i => (ε : ℂ) + 2 * i + 1 + pole ε r
    have hu : (range B).erase r = (range m).erase r ∪ Ico m B := by
      ext i
      simp only [mem_erase, mem_range, mem_union, mem_Ico]
      omega
    have hdisj : Disjoint ((range m).erase r) (Ico m B) := by
      apply disjoint_left.mpr
      intro i hi hj
      have hi' := (mem_erase.mp hi).2
      simp only [mem_range] at hi'
      have hj' := mem_Ico.mp hj
      omega
    have hsplit : (∏ i ∈ (range B).erase r, d i) =
        (∏ i ∈ (range m).erase r, d i) * ∏ i ∈ Ico m B, d i := by
      rw [hu, prod_union hdisj]
    have hnum : (∏ i ∈ range m, a i) = a r * ∏ i ∈ (range m).erase r, a i :=
      (mul_prod_erase (range m) a (mem_range.mpr hrm)).symm
    have hden : (∏ i ∈ (range m).erase r, d i) ≠ 0 :=
      poleComplement_ne_zero ε m r
    simp only [regularizedSeq, hrm, ↓reduceIte, prod_div_distrib]
    change (∏ i ∈ range m, a i) * (∏ i ∈ Ico m B, d i) =
      (∏ i ∈ (range B).erase r, d i) *
        (a r * ((∏ i ∈ (range m).erase r, a i) / (∏ i ∈ (range m).erase r, d i)))
    rw [hsplit, hnum]
    field_simp

theorem clearedMultiplier_at_pole {σ : Type*} (ε : ℤ) {B r : ℕ}
    (hr : r < B) (q : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hq : eval z q = pole ε r) (j : ℤ) (hj : j.natAbs / 2 ≤ B) :
    eval z (clearedMultiplier ε B q j) =
      poleComplement ε B r * regularizedMultiplier (pole ε r) ε r j := by
  have hh := clearedSeq_at_pole ε hr hj q z hq
  simp only [clearedMultiplier, regularizedMultiplier, extend]
  split_ifs
  · exact hh
  · simp only [map_mul, eval_C]
    rw [hh]
    ring

def tailScale (ε : ℤ) (B r : ℕ) : ℂ :=
  poleComplement ε B r * regularizedSeq (pole ε r) ε r (r + 1)

theorem tailScale_ne_zero {ε : ℤ} (hε : ε = 0 ∨ ε = 1) (B r : ℕ) :
    tailScale ε B r ≠ 0 :=
  mul_ne_zero (poleComplement_ne_zero ε B r) (regularized_base_ne_zero hε r)

theorem clearedMultiplier_tail {σ : Type*} {ℓ B r : ℕ} {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (hl : ℓ = ε.toNat + 2 * r + 1) (hr : r < B)
    (q : MvPolynomial σ ℂ) (z : σ → ℂ) (hq : eval z q = pole ε r)
    (j : ℤ) (hj : j.natAbs / 2 ≤ B) :
    eval z (clearedMultiplier ε B q j) =
      tailScale ε B r * tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j := by
  have ht : regularizedMultiplier (pole ε r) ε r j =
      regularizedSeq (pole ε r) ε r (r + 1) *
        tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j :=
    regularizedMultiplier_eq_tail hε r hl j
  rw [clearedMultiplier_at_pole ε hr q z hq j hj, ht]
  exact (mul_assoc _ _ _).symm

def positiveScale (ℓ B : ℕ) (ε : ℤ) : ℂ :=
  (∏ i ∈ range B, ((ε : ℂ) + 2 * i + 1 + (ℓ : ℂ))) / binomialSeq ℓ ε 0

theorem positiveScale_ne_zero {ℓ : ℕ} {ε : ℤ} (hℓ : 0 < ℓ)
    (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε)) (B : ℕ) :
    positiveScale ℓ B ε ≠ 0 := by
  apply div_ne_zero _ (binomial_base_ne_zero hℓ hε hpar)
  apply prod_ne_zero_iff.mpr
  intro i _
  exact genericSeq_denom_ne_zero
    (by simpa using (show (0 : ℝ) < ℓ by exact_mod_cast hℓ)) (by omega : 0 ≤ ε) i

theorem clearedMultiplier_binomial {σ : Type*} {ℓ B : ℕ} {ε : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε))
    (q : MvPolynomial σ ℂ) (z : σ → ℂ) (hq : eval z q = (ℓ : ℂ))
    (j : ℤ) (hj : j.natAbs / 2 ≤ B) :
    eval z (clearedMultiplier ε B q j) = positiveScale ℓ B ε * binomialMultiplier ℓ ε j := by
  have hden : eval z (denominator ε B q) ≠ 0 := by
    apply denominator_ne_zero_of_re_pos (by omega : 0 ≤ ε)
    rw [hq]
    simpa using (show (0 : ℝ) < ℓ by exact_mod_cast hℓ)
  rw [← clear_multiplier ε q j hj z hden, hq,
    binomialMultiplier_eq_generic hℓ hε hpar j, positiveScale]
  have hd := eval_denominator ε B q z
  rw [hq] at hd
  rw [hd]
  field_simp [binomial_base_ne_zero hℓ hε hpar]

section Spectral

variable {σ W : Type*} [AddCommGroup W] [Module ℂ W]

theorem clearedSpectral_tail {ℓ B r : ℕ} {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (hl : ℓ = ε.toNat + 2 * r + 1) (hr : r < B)
    (π : ℤ → Module.End ℂ W) (S : Finset ℤ)
    (hB : ∀ j ∈ S, j.natAbs / 2 ≤ B)
    (q : MvPolynomial σ ℂ) (z : σ → ℂ) (hq : eval z q = pole ε r) :
    clearedSpectral π S ε B q z =
      tailScale ε B r • spectralMultiplier π S (tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs)) := by
  unfold clearedSpectral spectralMultiplier
  rw [smul_sum]
  apply sum_congr rfl
  intro j hj
  rw [clearedMultiplier_tail hε hl hr q z hq j (hB j hj), smul_smul]

theorem clearedSpectral_binomial {ℓ B : ℕ} {ε : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε))
    (π : ℤ → Module.End ℂ W) (S : Finset ℤ)
    (hB : ∀ j ∈ S, j.natAbs / 2 ≤ B)
    (q : MvPolynomial σ ℂ) (z : σ → ℂ) (hq : eval z q = (ℓ : ℂ)) :
    clearedSpectral π S ε B q z =
      positiveScale ℓ B ε • spectralMultiplier π S (binomialMultiplier ℓ ε) := by
  unfold clearedSpectral spectralMultiplier
  rw [smul_sum]
  apply sum_congr rfl
  intro j hj
  rw [clearedMultiplier_binomial hℓ hε hpar q z hq j (hB j hj), smul_smul]

end Spectral

theorem compact_tail {ℓ N r p : ℕ} {ε : ℤ}
    (hp : p + 1 < 3) (hε : ε = 0 ∨ ε = 1)
    (hl : ℓ = ε.toNat + 2 * r + 1) (hr : r < N)
    (q : PV) (z : Parameters) (hq : eval z q = pole ε r) :
    compactCleared N hp ε q z =
      tailScale ε N r • spectralMultiplier (RealOrthogonalUncertainty.proj N hp)
        (Icc (-(N : ℤ)) N) (tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs)) := by
  apply clearedSpectral_tail hε hl hr _ _ _ q z hq
  intro j hj
  have hb := mem_Icc.mp hj
  omega

theorem compact_binomial {ℓ N p : ℕ} {ε : ℤ}
    (hp : p + 1 < 3) (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε))
    (q : PV) (z : Parameters) (hq : eval z q = (ℓ : ℂ)) :
    compactCleared N hp ε q z =
      positiveScale ℓ N ε • spectralMultiplier (RealOrthogonalUncertainty.proj N hp)
        (Icc (-(N : ℤ)) N) (binomialMultiplier ℓ ε) := by
  apply clearedSpectral_binomial hℓ hε hpar _ _ _ q z hq
  intro j hj
  have hb := mem_Icc.mp hj
  omega

end Langlands.Archimedean.RealClearedCompactDegeneration

namespace Langlands.Archimedean

open MvPolynomial RealBlockMultiplier RealRationalCompactFamilies
  RealSignedTailPolynomial RealClearedCompactDegeneration

/-- Nonzero binomial and canonical-tail specialization constants in one finite compact model. -/
def RealClearedCompactDegenerationStatement : Prop :=
  ∀ (N p ℓ : ℕ) (hp : p + 1 < 3) (ε : ℤ),
    0 < ℓ → (ε = 0 ∨ ε = 1) → Even ((ℓ : ℤ) - 1 - ε) →
    (∃ C : ℂ, C ≠ 0 ∧ ∀ (q : PV) (z : Parameters), eval z q = (ℓ : ℂ) →
      compactCleared N hp ε q z =
        C • spectralMultiplier (RealOrthogonalUncertainty.proj N hp)
          (Finset.Icc (-(N : ℤ)) N) (binomialMultiplier ℓ ε)) ∧
    (∀ r : ℕ, ℓ = ε.toNat + 2 * r + 1 → r < N →
      ∃ C : ℂ, C ≠ 0 ∧ ∀ (q : PV) (z : Parameters), eval z q = pole ε r →
        compactCleared N hp ε q z =
          C • spectralMultiplier (RealOrthogonalUncertainty.proj N hp)
            (Finset.Icc (-(N : ℤ)) N)
            (tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs)))

theorem realClearedCompactDegeneration : RealClearedCompactDegenerationStatement :=
  fun N _ _ hp _ hℓ hε hpar =>
    ⟨⟨_, positiveScale_ne_zero hℓ hε hpar N,
        fun q z hq => compact_binomial hp hℓ hε hpar q z hq⟩,
      fun r hl hr => ⟨_, tailScale_ne_zero hε N r,
        fun q z hq => compact_tail hp hε hl hr q z hq⟩⟩

end Langlands.Archimedean
