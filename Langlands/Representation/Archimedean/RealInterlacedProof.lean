import Langlands.Representation.Archimedean.RealInterlacedEngine

/-!
# The linked Jacquet functional for two interlaced induction blocks

The chain of multipliers for two interlaced linked induction blocks `[d, e]` of `GL₄(ℝ)`, in the
case `|m(e)| ≤ |m(d)|` (that is `A ≥ C`), and the explicit values of its test vectors.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealInterlacedJacquet

open Langlands.LocalFactor.Archimedean
open RealJacquetFrobenius RealBlockJacquet RealBlockMultiplier RealBlockRotation
  RealBlockFourierFinite RealBlockDerivative RealCharacterCrossing RealBlockFlatJacquet InductionStages GramFormula

/-! ## Positions of `GL₄` -/

section Positions

theorem ia40 : ia h40 = (0 : Fin 4) := rfl
theorem ib40 : ib h40 = (1 : Fin 4) := rfl
theorem ia41 : ia h41 = (1 : Fin 4) := rfl
theorem ib41 : ib h41 = (2 : Fin 4) := rfl
theorem ia42 : ia h42 = (2 : Fin 4) := rfl
theorem ib42 : ib h42 = (3 : Fin 4) := rfl

theorem sw40_0 : sw h40 (0 : Fin 4) = 1 := sw_ia h40
theorem sw40_1 : sw h40 (1 : Fin 4) = 0 := sw_ib h40
theorem sw40_2 : sw h40 (2 : Fin 4) = 2 := sw_of_ne h40 (by decide) (by decide)
theorem sw40_3 : sw h40 (3 : Fin 4) = 3 := sw_of_ne h40 (by decide) (by decide)
theorem sw41_0 : sw h41 (0 : Fin 4) = 0 := sw_of_ne h41 (by decide) (by decide)
theorem sw41_1 : sw h41 (1 : Fin 4) = 2 := sw_ia h41
theorem sw41_2 : sw h41 (2 : Fin 4) = 1 := sw_ib h41
theorem sw41_3 : sw h41 (3 : Fin 4) = 3 := sw_of_ne h41 (by decide) (by decide)
theorem sw42_0 : sw h42 (0 : Fin 4) = 0 := sw_of_ne h42 (by decide) (by decide)
theorem sw42_1 : sw h42 (1 : Fin 4) = 1 := sw_of_ne h42 (by decide) (by decide)
theorem sw42_2 : sw h42 (2 : Fin 4) = 3 := sw_ia h42
theorem sw42_3 : sw h42 (3 : Fin 4) = 2 := sw_ib h42

theorem neg_one_pow_congr {a b : ℕ} (h : a % 2 = b % 2) : (-1 : ℂ) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

theorem neg_one_pow_mod_flip (p : ℕ) : (-1 : ℂ) ^ (p % 2) = -(-1) ^ ((p + 1) % 2) := by
  rw [← neg_one_pow_eq_pow_mod_two, ← neg_one_pow_eq_pow_mod_two, pow_succ]
  ring

end Positions

/-! ## Fourier coefficients of the final functions -/

section Coefficients

theorem coeff_ne_zero_of_eq {F G : ℝ → ℂ} {j : ℤ} (h : ∀ θ, F θ = G θ) (hG : coeff j G ≠ 0) :
    coeff j F ≠ 0 := by
  rwa [show F = G from funext h]

/-- The coefficient used for the nonvanishing of the top coefficient: along `r₁(t) κ₀` the
function `c (i e^{-it} + i)^m + (-1)^s c (i e^{-it} - i)^m` with `c ≠ 0` has a nonzero
coefficient at `-(m - s)`. -/
theorem coeff_pair_neg_ne_zero {c : ℂ} (hc : c ≠ 0) (m s : ℕ) (hsm : s ≤ m) :
    coeff (-((m - s : ℕ) : ℤ)) (fun t => c * (Complex.I * expMode (-1) t + Complex.I) ^ m +
      (-1) ^ s * c * (Complex.I * expMode (-1) t + -Complex.I) ^ m) ≠ 0 := by
  rw [show -((m - s : ℕ) : ℤ) = (-1) * ((m - s : ℕ) : ℤ) by ring,
    coeff_binom_pair (by norm_num) _ _ _ _ _ _ m (Nat.sub_le m s)]
  have hms : m - (m - s) = s := by omega
  rw [hms]
  intro h
  have h1 : (-1 : ℂ) ^ s * (-Complex.I) ^ s = Complex.I ^ s := by
    rw [← mul_pow]
    ring
  have h2 : 2 * (Real.pi : ℂ) * (m.choose (m - s) : ℂ) *
      (2 * (c * (Complex.I ^ (m - s) * Complex.I ^ s))) = 0 := by
    rw [← h]
    linear_combination (-(2 * (Real.pi : ℂ) * (m.choose (m - s) : ℂ) * c *
      Complex.I ^ (m - s))) * h1
  have hc' : m.choose (m - s) ≠ 0 := (Nat.choose_pos (Nat.sub_le m s)).ne'
  simp [Real.pi_ne_zero, Complex.I_ne_zero, hc, hc'] at h2

/-- The final coefficient: `2π g ((i e^{iθ} + 1)^m - (-1)^s (-i e^{iθ} + 1)^m)` has a nonzero
coefficient at `(1 + s) mod 2`. -/
theorem coeff_pair_pos_ne_zero {g : ℂ} (hg : g ≠ 0) (m s : ℕ) (hs : s ≤ 1) (hm : 0 < m) :
    coeff (((1 + s) % 2 : ℕ) : ℤ) (fun θ =>
      2 * (Real.pi : ℂ) * g * (Complex.I * expMode 1 θ + 1) ^ m +
        -(2 * (Real.pi : ℂ) * g * (-1) ^ s) * (-Complex.I * expMode 1 θ + 1) ^ m) ≠ 0 := by
  have hj : (1 + s) % 2 ≤ m := by omega
  rw [show (((1 + s) % 2 : ℕ) : ℤ) = 1 * (((1 + s) % 2 : ℕ) : ℤ) by ring,
    coeff_binom_pair one_ne_zero _ _ _ _ _ _ m hj]
  intro h
  have hsj : s + (1 + s) % 2 = 1 := by omega
  have h1 : (-1 : ℂ) ^ s * (-Complex.I) ^ ((1 + s) % 2) = -Complex.I ^ ((1 + s) % 2) := by
    rw [neg_pow Complex.I, ← mul_assoc, ← pow_add, hsj, pow_one]
    ring
  have h2 : 2 * (Real.pi : ℂ) * (m.choose ((1 + s) % 2) : ℂ) *
      (2 * (Real.pi : ℂ) * g * (2 * Complex.I ^ ((1 + s) % 2))) = 0 := by
    rw [← h]
    linear_combination (2 * (Real.pi : ℂ) * (m.choose ((1 + s) % 2) : ℂ) *
      (2 * (Real.pi : ℂ) * g)) * h1
  have hc : m.choose ((1 + s) % 2) ≠ 0 := (Nat.choose_pos hj).ne'
  simp [Real.pi_ne_zero, Complex.I_ne_zero, hc, hg] at h2

end Coefficients

/-! ## Multipliers -/

section Multipliers

/-- The sign multiplier solves the recurrence for `δ = 1` on the odd class. -/
theorem isRecurrent_sign_one :
    IsRecurrent (1 - ((0 : ℕ) : ℂ)) (((1 : ℕ) : ℤ)) (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) := by
  intro j hj
  simp only [Nat.cast_zero, sub_zero]
  rw [Int.even_iff] at hj
  rcases lt_trichotomy j (-1) with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg (by omega : j + 2 < 0), Int.sign_eq_neg_one_of_neg (by omega)]
    push_cast
    ring
  · subst h
    norm_num
  · rw [Int.sign_eq_one_of_pos (by omega : 0 < j + 2), Int.sign_eq_one_of_pos (by omega)]
    push_cast
    ring

/-- **The tail step.** A solution of the recurrence for `δ = 1 - B` on the class `B + 1`,
symmetric for `(-1)^{B+1}`, nonzero at a mode `|j| > B` of that class: the tail multiplier for
`B > 0` and the sign multiplier for `B = 0`. -/
theorem exists_tail_mult {B ε : ℕ} (hε : ε = (B + 1) % 2) {j : ℤ} (hj : (B : ℤ) < |j|)
    (hjε : Even (j - ε)) :
    ∃ μ : ℤ → ℂ, IsRecurrent (1 - (B : ℂ)) (ε : ℤ) μ ∧ IsSymmetric (ε : ℤ) ((-1) ^ ε) μ ∧
      μ j ≠ 0 := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    have hε1 : ε = 1 := by omega
    subst hε1
    refine ⟨fun j : ℤ => ((Int.sign j : ℤ) : ℂ), isRecurrent_sign_one, ?_, ?_⟩
    · rw [pow_one]
      exact isSymmetric_sign _
    · have hj0 : j ≠ 0 := by
        rintro rfl
        simp at hj
      simpa [Int.sign_eq_zero_iff_zero] using hj0
  · have hε' : (ε : ℤ) = 0 ∨ (ε : ℤ) = 1 := by omega
    have hpar : Even ((B : ℤ) - 1 - ε) := by
      rw [Int.even_iff]
      omega
    have hσ : ((-1 : ℂ) ^ ε) ^ 2 = 1 := neg_one_pow_sq ε
    refine ⟨tailMultiplier B ε ((-1) ^ ε), isRecurrent_tailMultiplier hB hε' hpar hσ,
      isSymmetric_tailMultiplier hB hε' hpar hσ, ?_⟩
    exact (tailMultiplier_ne_zero_iff hB hε' hpar hσ hjε).mpr hj

end Multipliers

/-! ## The case `A ≥ C` -/

section AC

/-- The first column `e₁` of the test functions for `A ≥ C`. -/
def uA : Fin 4 → ℂ := ![0, 1, 0, 0]

/-- The second column `-e₀ - i e₂ - e₃` of the test functions for `A ≥ C`. -/
def uB : Fin 4 → ℂ := ![-1, 0, -Complex.I, -1]

theorem colv_uA_one : colv uA 0 1 = 0 ∧ colv uA 1 1 = 1 ∧ colv uA 2 1 = 0 ∧ colv uA 3 1 = 0 := by
  simp [colv_one, uA]

theorem w_one_AC : w1 uA uB 1 = 1 ∧ w2 uA uB 1 = 1 ∧ w3 uA uB 1 = -Complex.I := by
  simp [w1, w2, w3, pl, colv_one, uA, uB]

/-- Values along `r₁(t) r₀(π/2)`. -/
theorem values_AC_kappa (t : ℝ) :
    yZ h40 uA ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
        ((blockRotation 4 0 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)) = -1 ∧
      yZb h40 uA ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
        ((blockRotation 4 0 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)) = -1 ∧
      nup uA uB ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
        ((blockRotation 4 0 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)) =
          Complex.I * expMode (-1) t + Complex.I ∧
      num uA uB ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
        ((blockRotation 4 0 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)) =
          Complex.I * expMode (-1) t + -Complex.I := by
  obtain ⟨a0, a1, -, -⟩ := colv_rot1 uA t
    ((blockRotation 4 0 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)
  obtain ⟨b0, b1, b2, -⟩ := colv_rot0 uA (Real.pi / 2) 1
  obtain ⟨-, c2, c3⟩ := w_rot1 uA uB t
    ((blockRotation 4 0 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)
  obtain ⟨d1, d2, d3⟩ := w_rot0 uA uB (Real.pi / 2) 1
  obtain ⟨o0, o1, o2, -⟩ := colv_uA_one
  obtain ⟨p1, p2, p3⟩ := w_one_AC
  simp only [yZ0_apply, yZb0_apply, nup, num, a0, a1, b0, b1, b2, c2, c3, d1, d2, d3, o0, o1,
    o2, p1, p2, p3, Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.ofReal_zero,
    Complex.ofReal_one, expMode_neg_one_eq]
  refine ⟨by ring, by ring, ?_, ?_⟩
  · linear_combination (Real.sin t : ℂ) * Complex.I_sq
  · linear_combination (Real.sin t : ℂ) * Complex.I_sq

theorem yZ1_fl32 (u : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    yZ h41 u (fl 3 * (fl 2 * X)) = colv u 1 X - Complex.I * colv u 2 X := by
  simp only [yZ1_apply, colv_fl3fl]
  norm_num
  ring

/-- Values along `r₂(θ)` and `s₃ s₂ r₂(θ)`. -/
theorem values_AC_rot2 (r m : ℕ) (θ : ℝ) :
    (yZ h41 uA ^ r * wp uA uB ^ m) (blockRotation 4 2 θ : Matrix (Fin 4) (Fin 4) ℝ) =
        (Complex.I * expMode 1 θ + 1) ^ m ∧
      (yZ h41 uA ^ r * wp uA uB ^ m)
          (fl 3 * (fl 2 * (blockRotation 4 2 θ : Matrix (Fin 4) (Fin 4) ℝ))) =
        (-Complex.I * expMode 1 θ + 1) ^ m := by
  set R : Matrix (Fin 4) (Fin 4) ℝ := (blockRotation 4 2 θ : Matrix (Fin 4) (Fin 4) ℝ) with hR
  have e : R = (blockRotation 4 2 θ : Matrix (Fin 4) (Fin 4) ℝ) * 1 := (mul_one _).symm
  obtain ⟨-, a1, a2, -⟩ := colv_rot2 uA θ 1
  obtain ⟨b1, b2, -⟩ := w_rot2 uA uB θ 1
  obtain ⟨-, o1, o2, o3⟩ := colv_uA_one
  obtain ⟨p1, p2, p3⟩ := w_one_AC
  obtain ⟨f1, f2, -⟩ := w_fl32 uA uB R
  have hy : yZ h41 uA R = 1 := by
    rw [yZ1_apply, e, a1, a2, o1, o2, o3]
    ring
  have hy' : yZ h41 uA (fl 3 * (fl 2 * R)) = 1 := by
    rw [yZ1_fl32, e, a1, a2, o1, o2, o3]
    ring
  have hw1 : w1 uA uB R = 1 := by rw [e, b1, p1]
  have hw2 : w2 uA uB R = expMode 1 θ := by
    rw [e, b2, p2, p3, expMode_one_eq]
    ring
  have hw : wp uA uB R = Complex.I * expMode 1 θ + 1 := by
    rw [wp_apply, hw1, hw2]
    ring
  have hw' : wp uA uB (fl 3 * (fl 2 * R)) = -Complex.I * expMode 1 θ + 1 := by
    rw [wp_apply, f1, f2, hw1, hw2]
    ring
  constructor
  · simp only [Pi.mul_apply, Pi.pow_apply, hy, hw, one_pow, one_mul]
  · simp only [Pi.mul_apply, Pi.pow_apply, hy', hw', one_pow, one_mul]

/-- **The engine for `A ≥ C`.** Let `p = |m(d)| ≥ q = |m(e)|`, `C = k`, `B = q - k`,
`A = p - q + k`, `r + m = p + 1`. Given the flat functional `ψ₀` at the block `2` (exponents
`a₀`, signs `e₀`, values `μ₀(±m)`) and a tail multiplier `μ₁` at the middle block, the chain
`ψ₀`, tail at `1`, generic at `0`, followed by the dichotomy at `1` and the final binomial
functional at `2`, gives the conclusion. -/
theorem engine_AC {d e : ComplexCharacterData} {p q k r m : ℕ}
    (hpd : d.weight.natAbs = p) (hqe : e.weight.natAbs = q) (hk : 0 < k) (hkq : k ≤ q)
    (hqp : q ≤ p) (hrm : r + m = p + 1) (hmq : q ≤ m) (hmpar : (m + q) % 2 = 1)
    {μ0 : ℤ → ℂ} {a0 : Fin 4 → ℂ} {e0 : Fin 4 → Fin 2}
    (hψ0 : IsRealJacquetFunctional 4 (realStandardRep 4 [RealBlock.induced d, RealBlock.induced e])
      (realStandardLie 4 [RealBlock.induced d, RealBlock.induced e])
      (blockJacquet 4 [RealBlock.induced d, RealBlock.induced e] 2 μ0) a0 e0)
    (hA : expo a0 0 - expo a0 2 = ((p - q + k : ℕ) : ℂ))
    (hB : expo a0 1 - expo a0 2 = -((q - k : ℕ) : ℂ))
    (hP : expo a0 0 - expo a0 1 = (p : ℂ))
    (hC : expo a0 1 - expo a0 3 = (k : ℂ))
    (he0 : (e0 0).val = (p + 1) % 2) (he1 : (e0 1).val = 0)
    (he2 : (e0 2).val = (q + 1 + k % 2) % 2) (he3 : (e0 3).val = k % 2)
    (hμ0p : μ0 (m : ℤ) = 1) (hμ0m : μ0 (-(m : ℤ)) = (-1) ^ (k % 2))
    {μ1 : ℤ → ℂ} (hrec1 : IsRecurrent (1 - ((q - k : ℕ) : ℂ)) (((q + 1 + k) % 2 : ℕ) : ℤ) μ1)
    (hsym1 : IsSymmetric (((q + 1 + k) % 2 : ℕ) : ℤ) ((-1) ^ ((q + 1 + k) % 2)) μ1)
    (hμ1 : μ1 (-((m - k % 2 : ℕ) : ℤ)) ≠ 0) :
    RealLinkedJacquetFunctionalExists 4 [RealBlock.induced d, RealBlock.induced e] := by
  -- the tail step at the middle block
  have hpar1 : par h41 e0 = (q + 1 + k) % 2 := by
    unfold par
    rw [ia41, ib41, he1, he2]
    omega
  have hδ1 : expo a0 (ia h41) - expo a0 (ib h41) + 1 = 1 - ((q - k : ℕ) : ℂ) := by
    rw [ia41, ib41, hB]
    ring
  have hJ1 := isJacquet_cross h41 (expo a0) e0 (μ := μ1) (by rw [hδ1, hpar1]; exact hrec1)
    (by rw [hpar1]; exact hsym1)
  -- the generic step at the block `0`
  have hx1 : ∀ i, expo (crossExp h41 (expo a0)) i = expo a0 (sw h41 i) := fun i => by
    rw [expo_crossExp]
    rfl
  have hpar2 : par h40 (e0 ∘ sw h41) = (p + q + k) % 2 := by
    unfold par
    simp only [Function.comp_apply]
    rw [ia40, ib40, sw41_0, sw41_1, he0, he2]
    omega
  set ε2 : ℤ := ((par h40 (e0 ∘ sw h41) : ℕ) : ℤ) with hε2def
  have hε2 : ε2 = 0 ∨ ε2 = 1 := par_cases h40 _
  have hν : 0 < (((p - q + k : ℕ) : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (by omega : 0 < p - q + k)
  have hδ2 : expo (crossExp h41 (expo a0)) (ia h40) - expo (crossExp h41 (expo a0)) (ib h40) + 1 =
      ((p - q + k : ℕ) : ℂ) + 1 := by
    rw [hx1, hx1, ia40, ib40, sw41_0, sw41_1, hA]
  have hsym2 : IsSymmetric (par h40 (e0 ∘ sw h41)) ((-1) ^ par h40 (e0 ∘ sw h41))
      (genericMultiplier ((p - q + k : ℕ) : ℂ) ε2) := by
    exact isSymmetric_genericMultiplier ((p - q + k : ℕ) : ℂ) hε2
  have hJ2 := isJacquet_cross h40 (expo (crossExp h41 (expo a0))) (e0 ∘ sw h41)
    (by rw [hδ2]; exact isRecurrent_genericMultiplier hν hε2) hsym2
  have hμ2 : ∀ j, genericMultiplier ((p - q + k : ℕ) : ℂ) ε2 j ≠ 0 := by
    refine genericMultiplier_ne_zero hν hε2 fun m' h => ?_
    have h' : ((p - q + k : ℕ) : ℤ) = ε2 + 2 * m' + 1 := by exact_mod_cast h
    rw [hε2def, hpar2] at h'
    omega
  -- the exponents and signs after the two steps
  have hT : ∀ i, expo (crossExp h40 (expo (crossExp h41 (expo a0)))) i =
      expo a0 (sw h41 (sw h40 i)) := fun i => by
    rw [expo_crossExp, expo_crossExp]
    rfl
  have hE0 : ((e0 ∘ sw h41) ∘ sw h40) 0 = e0 2 := by
    simp only [Function.comp_apply, sw40_0, sw41_1]
  have hE1 : ((e0 ∘ sw h41) ∘ sw h40) 1 = e0 0 := by
    simp only [Function.comp_apply, sw40_1, sw41_0]
  have hE2 : ((e0 ∘ sw h41) ∘ sw h40) 2 = e0 1 := by
    simp only [Function.comp_apply, sw40_2, sw41_2]
  have hE3 : ((e0 ∘ sw h41) ∘ sw h40) 3 = e0 3 := by
    simp only [Function.comp_apply, sw40_3, sw41_3]
  -- the flipped signs of the final functional
  obtain ⟨e', he'0, he'1, he'2, he'3⟩ : ∃ e' : Fin 4 → Fin 2, e' 0 = e0 2 ∧
      (e' 1).val = p % 2 ∧ (e' 2).val = 1 ∧ e' 3 = e0 3 :=
    ⟨![e0 2, ⟨p % 2, Nat.mod_lt _ two_pos⟩, 1, e0 3], rfl, rfl, rfl, rfl⟩
  have hpar3 : par h42 e' = (1 + k % 2) % 2 := by
    unfold par
    rw [ia42, ib42, he'2, he'3, he3]
  refine exists_of_dichotomy ((frobMap hJ2).comp ((frobMap hJ1).comp (frobMap hψ0)))
    (fun κ v => ?_) (fun Y v => ?_) h41 (k₁ := p) (by omega) ?_ ?_ (e' := e') ?_ ?_ ?_ h42
    (k₂ := k) hk ?_ ?_ ?_
  · simp only [LinearMap.comp_apply, frobMap_rep]
  · simp only [LinearMap.comp_apply, frobMap_lie]
  · rw [hT, hT, ia41, ib41, sw40_1, sw41_0, sw40_2, sw41_2, hP]
  · rw [ia41, ib41, hE1, hE2, he0, he1, Nat.odd_iff]
    omega
  · intro i h1 h2
    fin_cases i
    · show e' 0 = ((e0 ∘ sw h41) ∘ sw h40) 0
      rw [he'0, hE0]
    · exact absurd rfl h1
    · exact absurd rfl h2
    · show e' 3 = ((e0 ∘ sw h41) ∘ sw h40) 3
      rw [he'3, hE3]
  · rw [ia41, he'1, hE1, he0]
    exact neg_one_pow_mod_flip p
  · rw [ib41, he'2, hE2, he1]
    norm_num
  · rw [hT, hT, ia42, ib42, sw40_2, sw41_2, sw40_3, sw41_3, hC]
  · rw [ia42, ib42, he'2, he'3, he3, Nat.odd_iff]
    omega
  -- the main evaluation
  intro hwin
  have hQ0 : (-1 : ℂ) ^ (![r + m, 0, m, 0] : Fin 4 → ℕ) 0 = (-1) ^ (d.weight.natAbs + 1) := by
    show (-1 : ℂ) ^ (r + m) = _
    rw [hrm, hpd]
  have hQ2 : (-1 : ℂ) ^ (![r + m, 0, m, 0] : Fin 4 → ℕ) 2 = (-1) ^ (e.weight.natAbs + 1) := by
    show (-1 : ℂ) ^ m = _
    rw [hqe]
    exact neg_one_pow_congr (by omega)
  obtain ⟨v, hv⟩ := exists_test_of (d := d) (e := e) (Fp_mem_PF h40 uA uB r m)
    (isSignEq_Fp0 uA uB r m) hQ0 (by simp) hQ2 (by simp) (Fp0_rot0 uA uB r m)
    (by rw [hpd, abs_of_nonneg (Int.natCast_nonneg _)]; omega) (Fp0_rot2 uA uB r m)
    (by rw [hqe, abs_of_nonneg (Int.natCast_nonneg _)]; omega)
  refine ⟨v, ?_⟩
  -- the first step on `SO(4)`
  set H1 : MF 4 := Gp h40 uA uB r m + (-1 : ℂ) ^ (k % 2) • Gm h40 uA uB r m with hH1def
  have hH1 : H1 ∈ Sm uA uB r m :=
    Submodule.add_mem _ (Gp_mem_Sm h40 uA uB r m)
      (Submodule.smul_mem _ _ (Gm_mem_Sm h40 uA uB r m))
  have hw0 : ∀ κ ∈ SOset 4, ((frobMap hψ0 v : KF 4 _) : Langlands.GeneralLinear 4 ℝ → ℂ) κ =
      H1 (κ : Matrix (Fin 4) (Fin 4) ℝ) := by
    intro κ hκ
    rw [frobMap_eq_two_mode hψ0 v (N := (m : ℤ)) (by omega)
      (test_two_mode hv (Fp0_rot2 uA uB r m)) hκ, hμ0p, hμ0m, hH1def]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- the value along `r₁(t) r₀(π/2)`
  have hval : coeff (-((m - k % 2 : ℕ) : ℤ)) (fun t => H1
      ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
        ((blockRotation 4 0 (Real.pi / 2) : Langlands.GeneralLinear 4 ℝ) :
          Matrix (Fin 4) (Fin 4) ℝ))) ≠ 0 := by
    refine coeff_ne_zero_of_eq (fun t => ?_)
      (coeff_pair_neg_ne_zero (pow_ne_zero r (by norm_num : (-1 : ℂ) ≠ 0)) m (k % 2) (by omega))
    obtain ⟨h1, h2, h3, h4⟩ := values_AC_kappa t
    have e : ((blockRotation 4 0 (Real.pi / 2) : Langlands.GeneralLinear 4 ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ) =
        (blockRotation 4 0 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1 := (mul_one _).symm
    rw [e, hH1def]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Gp_apply, Gm_apply, h1, h2, h3, h4]
    ring
  have hpar' : Even (((r + m : ℕ) : ℤ) - ((par h41 ((e0 ∘ sw h41) ∘ sw h40) : ℕ) : ℤ)) := by
    have : par h41 ((e0 ∘ sw h41) ∘ sw h40) = (p + 1) % 2 := by
      unfold par
      rw [ia41, ib41, hE1, hE2, he0, he1]
      omega
    rw [this, Int.even_iff]
    omega
  rw [hpar3]
  refine main_value (by omega) h40 (hasExpTop_Sm0 uA uB r m) hJ1 hJ2 hμ2 hH1 (frobMap hψ0 v) hw0
    (blockRotation_mem_SOset (n := 4) 0 (Real.pi / 2)) hμ1 hval (fun j hj κ hκ => hwin v j (by omega) κ hκ) hpar'
    (fun g hg => ?_)
  refine coeff_ne_zero_of_eq (fun θ => ?_)
    (coeff_pair_pos_ne_zero hg m (k % 2) (by omega) (by omega))
  obtain ⟨h1, h2⟩ := values_AC_rot2 r m θ
  simp only [h1, h2, hE2, hE3, he1, he3, zero_add]
  ring

/-- **The flat functional at the block `2`.** For `k` even the trivial multiplier, for `k` odd the
sign multiplier (flat since the block-`2` coefficients of weight `< |m(e)|` vanish), with the
natural signs at the blocks `0, 1` and the signs at the block `2` flipped for `k` odd. -/
theorem exists_flat_AC (d e : ComplexCharacterData) (k : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (μ0 : ℤ → ℂ) (e0 : Fin 4 → Fin 2),
      IsRealJacquetFunctional 4 (realStandardRep 4 [RealBlock.induced d, RealBlock.induced e])
        (realStandardLie 4 [RealBlock.induced d, RealBlock.induced e])
        (blockJacquet 4 [RealBlock.induced d, RealBlock.induced e] 2 μ0)
        (fun i : Fin 4 => realPositionExponent [RealBlock.induced d, RealBlock.induced e] (i : ℕ) +
          (((4 : ℕ) : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) e0 ∧
      (e0 0).val = (d.weight.natAbs + 1) % 2 ∧ (e0 1).val = 0 ∧
      (e0 2).val = (e.weight.natAbs + 1 + k % 2) % 2 ∧ (e0 3).val = k % 2 ∧
      μ0 (m : ℤ) = 1 ∧ μ0 (-(m : ℤ)) = (-1) ^ (k % 2) := by
  have hb2 : 2 + 1 < 4 := by norm_num
  have hτ := fun (i : Fin 4) (x : ℝ) =>
    realPositionCharacter_exp [RealBlock.induced d, RealBlock.induced e] i x
  have hc0 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 0 (-1) =
      (-1 : ℂ) ^ (d.weight.natAbs + 1) := realInducedFirstCharacter_neg_one d
  have hc1 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 1 (-1) = 1 :=
    realInducedSecondCharacter_neg_one d
  have hc2 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 2 (-1) =
      (-1 : ℂ) ^ (e.weight.natAbs + 1) := realInducedFirstCharacter_neg_one e
  have hc3 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 3 (-1) = 1 :=
    realInducedSecondCharacter_neg_one e
  have hpar : (-1 : ℂ) ^ ((e.weight.natAbs : ℤ) + 1) =
      realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 2 (-1) *
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] (2 + 1) (-1) := by
    show (-1 : ℂ) ^ ((e.weight.natAbs : ℤ) + 1) =
      realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 2 (-1) *
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 3 (-1)
    rw [hc2, hc3, mul_one, ← zpow_natCast]
    push_cast
    rfl
  set e0 : Fin 4 → Fin 2 := ![⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩, 0,
    ⟨(e.weight.natAbs + 1 + k % 2) % 2, Nat.mod_lt _ two_pos⟩, ⟨k % 2, Nat.mod_lt _ two_pos⟩]
    with he0def
  have hoff : ∀ i : Fin 4, i ≠ ia hb2 → i ≠ ib hb2 →
      (-1 : ℂ) ^ (e0 i).val = realPositionCharacter [RealBlock.induced d, RealBlock.induced e] i (-1) := by
    intro i h1 h2
    fin_cases i
    · show (-1 : ℂ) ^ ((d.weight.natAbs + 1) % 2) = _
      rw [hc0, ← neg_one_pow_eq_pow_mod_two]
    · show (-1 : ℂ) ^ 0 = _
      rw [hc1]
      ring
    · exact absurd rfl h1
    · exact absurd rfl h2
  rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
  · have hp' : (-1 : ℂ) ^ (e0 (ia hb2)).val =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 2 (-1) * 1 := by
      show (-1 : ℂ) ^ ((e.weight.natAbs + 1 + k % 2) % 2) = _
      rw [hk2, hc2, add_zero, mul_one, ← neg_one_pow_eq_pow_mod_two]
    have hq' : (-1 : ℂ) ^ (e0 (ib hb2)).val =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] (2 + 1) (-1) * 1 := by
      show (-1 : ℂ) ^ (k % 2) =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 3 (-1) * 1
      rw [hk2, hc3]
      ring
    have hm' : (1 : ℂ) = (-1) ^ (k % 2) := by
      rw [hk2]
      ring
    exact ⟨fun _ => 1, e0, isRealJacquetFunctional_blockJacquet_flat hb2 hτ hpar
      (fun _ _ _ => ⟨rfl, rfl⟩) (isSymmetric_one _) hoff hp' hq', rfl, rfl, rfl, rfl, rfl, hm'⟩
  · have hδ : (realPositionExponent [RealBlock.induced d, RealBlock.induced e] 2 +
          (((4 : ℕ) : ℂ) - 1) / 2 - ((2 : ℕ) : ℂ)) -
        (realPositionExponent [RealBlock.induced d, RealBlock.induced e] 3 +
          (((4 : ℕ) : ℂ) - 1) / 2 - ((3 : ℕ) : ℂ)) = (e.weight.natAbs : ℂ) + 1 := by
      show (e.exponent + (e.weight.natAbs : ℂ) / 2 + (((4 : ℕ) : ℂ) - 1) / 2 - ((2 : ℕ) : ℂ)) -
        (e.exponent - (e.weight.natAbs : ℂ) / 2 + (((4 : ℕ) : ℂ) - 1) / 2 - ((3 : ℕ) : ℂ)) =
          (e.weight.natAbs : ℂ) + 1
      push_cast
      ring
    have hp' : (-1 : ℂ) ^ (e0 (ia hb2)).val =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 2 (-1) * -1 := by
      show (-1 : ℂ) ^ ((e.weight.natAbs + 1 + k % 2) % 2) = _
      rw [hk2, hc2, ← neg_one_pow_eq_pow_mod_two]
      ring
    have hq' : (-1 : ℂ) ^ (e0 (ib hb2)).val =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] (2 + 1) (-1) * -1 := by
      show (-1 : ℂ) ^ (k % 2) =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 3 (-1) * -1
      rw [hk2, hc3]
      ring
    have hm1 : ((Int.sign (m : ℤ) : ℤ) : ℂ) = 1 := by
      rw [Int.sign_eq_one_of_pos (by omega)]
      simp
    have hm2 : ((Int.sign (-(m : ℤ)) : ℤ) : ℂ) = (-1) ^ (k % 2) := by
      rw [hk2, Int.sign_eq_neg_one_of_neg (by omega)]
      simp
    exact ⟨fun j : ℤ => ((Int.sign j : ℤ) : ℂ), e0,
      isRealJacquetFunctional_blockJacquet_flat hb2 hτ hpar
        (flat_sign hb2 hpar (w := e.weight.natAbs) ⟨0, by ring⟩
          (fun f j hj => (Submodule.mem_inf.mp f.2).1.2 2 e rfl j
            (by rwa [Int.abs_eq_natAbs e.weight]) 1) hδ)
        (isSymmetric_sign _) hoff hp' hq', rfl, rfl, rfl, rfl, hm1, hm2⟩

/-- **Two interlaced linked induction blocks with `|m(e)| ≤ |m(d)|`.** -/
theorem interlaced_AC {d e : ComplexCharacterData} {k : ℕ} (hk : 0 < k)
    (hkq : k ≤ e.weight.natAbs) (hqp : e.weight.natAbs ≤ d.weight.natAbs)
    (hlink : d.exponent - e.exponent =
      ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℕ) : ℂ) / 2 + k) :
    RealLinkedJacquetFunctionalExists 4 [RealBlock.induced d, RealBlock.induced e] := by
  have hlink' : d.exponent - e.exponent =
      ((d.weight.natAbs : ℂ) - e.weight.natAbs) / 2 + k := by
    rw [hlink, natAbs_sub_cast, min_eq_right hqp]
    ring
  obtain ⟨μ0, e0, hψ0, he0, he1, he2, he3, hμ0p, hμ0m⟩ := exists_flat_AC d e k
    (m := d.weight.natAbs + 1 - (d.weight.natAbs - e.weight.natAbs) % 2) (by omega)
  have hx : ∀ i : Fin 4, expo (fun i : Fin 4 =>
      realPositionExponent [RealBlock.induced d, RealBlock.induced e] (i : ℕ) +
        (((4 : ℕ) : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) i =
      realPositionExponent [RealBlock.induced d, RealBlock.induced e] (i : ℕ) := fun i => by
    simp only [expo]
    ring
  obtain ⟨μ1, hrec1, hsym1, hμ1⟩ := exists_tail_mult (B := e.weight.natAbs - k)
    (ε := (e.weight.natAbs + 1 + k) % 2) (by omega)
    (j := -((d.weight.natAbs + 1 - (d.weight.natAbs - e.weight.natAbs) % 2 - k % 2 : ℕ) : ℤ))
    (by rw [abs_neg, abs_of_nonneg (Int.natCast_nonneg _)]; omega)
    (by rw [Int.even_iff]; omega)
  refine engine_AC rfl rfl hk hkq hqp (r := (d.weight.natAbs - e.weight.natAbs) % 2)
    (m := d.weight.natAbs + 1 - (d.weight.natAbs - e.weight.natAbs) % 2) (by omega) (by omega) (by omega) hψ0 ?_ ?_ ?_ ?_ he0 he1 he2 he3 hμ0p hμ0m hrec1 hsym1 hμ1
  · rw [hx, hx]
    show (d.exponent + (d.weight.natAbs : ℂ) / 2) - (e.exponent + (e.weight.natAbs : ℂ) / 2) = _
    rw [Nat.cast_add, Nat.cast_sub hqp]
    linear_combination hlink'
  · rw [hx, hx]
    show (d.exponent - (d.weight.natAbs : ℂ) / 2) - (e.exponent + (e.weight.natAbs : ℂ) / 2) = _
    rw [Nat.cast_sub hkq]
    linear_combination hlink'
  · rw [hx, hx]
    show (d.exponent + (d.weight.natAbs : ℂ) / 2) - (d.exponent - (d.weight.natAbs : ℂ) / 2) = _
    ring
  · rw [hx, hx]
    show (d.exponent - (d.weight.natAbs : ℂ) / 2) - (e.exponent - (e.weight.natAbs : ℂ) / 2) = _
    linear_combination hlink'

end AC

end RealInterlacedJacquet

end Langlands.Archimedean
