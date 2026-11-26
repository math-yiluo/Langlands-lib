import Langlands.Global.RankinSelberg.RealGapAlternateColumnDecay
import Langlands.Global.RankinSelberg.RealGapAlternateRetained
import Langlands.Global.RankinSelberg.RealGapTorusBound

/-! # Joint logarithmic and unipotent decay in the real alternate gap chart -/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapAlternateTailBound

open ArchimedeanLocal (realSelfDualMeasure)
open RealGapAlternateColumnDecay (realGapAlternateColumnDecay unipotentDecay)
open RealGapAlternateRetained (height_retained_le firstRetainedColumn lastRetainedInverseRow retained_endpoint_norms)
open RealGapColumnFourier (triangularFourier)
open RealGapTorusBound (exponent_le_first blockLog_last)
open RealGapTriangularChart (Outer retainedMatrix)
open RealJacquetUnipotentMeasure (entryHaar)
open ComplexTwoBlockHaar (blockLog)
open RealConvergenceAnalysis (rootPos)

local notation "N" => fun q => Langlands.GeneralLinear.upperUnipotent (q + 1) ℝ
local notation "Col" => fun k q => Fin (k + q + 1) → ℝ
local notation "H" => realMatrixHeight

local instance gapAlternateTailNMeasurable (q : ℕ) : MeasurableSpace (N q) := borel _

/-- The product-order norm supplies a radial weight on the retained first column. -/
def headDecay {k : ℕ} (p : ℕ) (x : Fin k → ℝ) : ℝ := ((1 + ‖x‖) ^ p)⁻¹

/-- Summation of absolute values respects concatenation in consecutive blocks. -/
theorem sum_abs_append {k q : ℕ} (y : Fin k → ℝ) (z : Fin (q + 1) → ℝ) :
    (∑ i : Fin (k + (q + 1)), |Fin.append y z i|) = (∑ i, |y i|) + ∑ i, |z i| := by
  refine (Fin.sum_univ_add (a := k) (b := q + 1) (fun i => |Fin.append y z i|)).trans ?_
  simp only [Fin.append_left, Fin.append_right]

private theorem torus_bound {k q : ℕ} (A B T : ℝ) (hB : 0 ≤ B) (hT : A + 1 ≤ T) :
    ∃ (J : ℕ) (P Q : ℝ), 0 ≤ P ∧ 0 ≤ Q ∧ ∀ (y : Fin k → ℝ) (z : Fin (q + 1) → ℝ),
      A * (∑ i, |y i|) + B * (∑ i, |z i|) + T * (∑ i, y i) -
        (J : ℝ) * rootPos (Fin.append (m := k) (n := q + 1) y z) - P * max (z (Fin.last q)) 0 - Q * max (-z 0) 0 ≤
        - ((∑ i, |y i|) + ∑ i, |z i|) := by
  let n := k + q + 1
  let hkn : k < n := by omega
  let P := max (2 * T) (B + 1) * (((k + q : ℕ) : ℝ) + 1)
  let Q := (B + 1) * (n - k : ℕ)
  have hP : 0 ≤ P := mul_nonneg ((by linarith : 0 ≤ B + 1).trans (le_max_right _ _)) (by positivity)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  obtain ⟨J, hJ⟩ := exists_nat_ge (P + Q)
  refine ⟨J, P, Q, hP, hQ, fun y z => ?_⟩
  let e := finCongr (show n - k = q + 1 by omega)
  let e₀ := finCongr (Nat.add_sub_of_le hkn.le)
  let z' := z ∘ e
  have hX : blockLog hkn y z' = Fin.append (m := k) (n := q + 1) y z := by
    funext i
    refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
    · have he : e₀.symm (i₀.castAdd (q + 1)) = i₀.castAdd (n - k) := Fin.ext rfl
      change Fin.append y z' (e₀.symm (i₀.castAdd (q + 1))) = _
      rw [he, Fin.append_left, Fin.append_left]
    · have he : e₀.symm (i₁.natAdd k) = (e.symm i₁).natAdd k := Fin.ext rfl
      change Fin.append y z' (e₀.symm (i₁.natAdd k)) = _
      rw [he, Fin.append_right, Fin.append_right]
      exact congrArg z (e.apply_symm_apply i₁)
  have hZ : (∑ i, |z' i|) = ∑ i, |z i| := Fintype.sum_equiv e _ _ fun _ => rfl
  have h0 : z' ⟨0, Nat.sub_pos_of_lt hkn⟩ = z 0 := congrArg z (Fin.ext rfl)
  have hL : z' ⟨k + q - k, by dsimp only [n]; omega⟩ = z (Fin.last q) := by
    apply congrArg z
    apply Fin.ext
    change k + q - k = q
    omega
  have h := exponent_le_first hkn y z' hB hT (J := (J : ℝ)) (P := P) (Q := Q) hJ le_rfl le_rfl
  dsimp only at h
  rw [blockLog_last] at h
  rw [hX, hZ, h0, hL] at h
  exact h

private theorem schwartz_endpoint_decay {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] (Φ : 𝓢(E, ℂ)) (n P : ℝ) (hn : 1 ≤ n) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : E) (x : D) (t : ℝ), ‖x‖ ≤ n * ‖v‖ → Real.exp t ≤ n * ‖v‖ →
      ‖Φ v‖ ≤ C * ((1 + ‖x‖) ^ p)⁻¹ * Real.exp (-P * max t 0) := by
  obtain ⟨m, hm⟩ := exists_nat_ge P
  let S := (Finset.Iic (p + m, 0)).sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) Φ
  let C := n ^ (p + m) * ((2 : ℝ) ^ (p + m) * S)
  have hS : 0 ≤ S := apply_nonneg _ _
  have hn₀ := zero_le_one.trans hn
  refine ⟨C, mul_nonneg (pow_nonneg hn₀ _) (mul_nonneg (by positivity) hS), fun v x t hx ht => ?_⟩
  let U := 1 + ‖v‖
  let V := 1 + ‖x‖
  have hU : 1 ≤ U := le_add_of_nonneg_right (norm_nonneg _)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hnx : V ≤ n * U := by
    dsimp only [U, V]
    rw [mul_add, mul_one]
    exact add_le_add hn hx
  have hnt : Real.exp (max t 0) ≤ n * U := by
    rcases le_total t 0 with h | h
    · rw [max_eq_right h, Real.exp_zero]
      exact one_le_mul_of_one_le_of_one_le hn hU
    · rw [max_eq_left h]
      exact ht.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hn₀)
  have hExp : Real.exp (P * max t 0) ≤ (n * U) ^ m := by
    refine (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hm (le_max_right _ _))).trans ?_
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hnt _
  have hF : U ^ (p + m) * ‖Φ v‖ ≤ (2 : ℝ) ^ (p + m) * S := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (p + m, 0)) le_rfl le_rfl Φ v
    simpa only [norm_iteratedFDeriv_zero, U, S] using h
  rw [neg_mul, Real.exp_neg, mul_assoc, ← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (mul_pos (pow_pos hV _) (Real.exp_pos _))).mpr
  calc
    _ ≤ ‖Φ v‖ * ((n * U) ^ p * (n * U) ^ m) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ hV.le hnx _) hExp (Real.exp_nonneg _) ?_) (norm_nonneg _)
      exact pow_nonneg (mul_nonneg hn₀ (zero_le_one.trans hU)) _
    _ = n ^ (p + m) * (U ^ (p + m) * ‖Φ v‖) := by rw [← pow_add (n * U), mul_pow]; ring
    _ ≤ C := mul_le_mul_of_nonneg_left hF (pow_nonneg hn₀ _)

/-- The alternate tail tests absorb the fixed height and density growth and supply a separated
envelope: decay of the prescribed polynomial order `m` in the first column and an integrable
factor in the upper unipotent variable. The first-column factor is integrable for an additive
Haar measure once `m` exceeds the real dimension `k`. -/
def RealGapAlternateTailBoundStatement : Prop :=
  ∀ (k q : ℕ) (A B T : ℝ), 0 ≤ B → A + 1 ≤ T →
    ∀ (a : ℝˣ) (Φ Ψ : 𝓢(Col k q, ℂ)) (Ξ : Fin q → 𝓢(Col k q, ℂ)) (M m : ℕ),
      ∃ (J l : ℕ) (C : ℝ), 0 ≤ C ∧
        Integrable (unipotentDecay (q := q) l) (entryHaar (realSelfDualMeasure a) (q + 1)) ∧
        ∀ (y : Fin k → ℝ) (p : Outer k q) (Z : N q),
          H (retainedMatrix k q p) ^ M * ‖Φ (firstRetainedColumn p)‖ * ‖Ψ (lastRetainedInverseRow p)‖ *
            ‖triangularFourier k q a (retainedMatrix k q p) Ξ Z‖ *
            Real.exp (A * (∑ i, |y i|) + B * (∑ i, |p.1.1.2 i|) + T * (∑ i, y i) -
              (J : ℝ) * rootPos (Fin.append (m := k) (n := q + 1) y (-p.1.1.2))) ≤
            C * Real.exp (-∑ i, |y i|) * Real.exp (-∑ i, |p.1.1.2 i|) * headDecay m p.2 * unipotentDecay l Z

set_option maxHeartbeats 850000 in
theorem realGapAlternateTailBound : RealGapAlternateTailBoundStatement := by
  intro k q A B T hB hT a Φ Ψ Ξ M m
  obtain ⟨l, C₀, hC₀, hInt, hZ⟩ := realGapAlternateColumnDecay k q a Ξ
  let L := M + l
  let n := ((k + q + 1 : ℕ) : ℝ)
  let K := (1 + 2 * n ^ 2) * (2 * n ^ 2)
  have hn : 1 ≤ n := by dsimp only [n]; exact_mod_cast Nat.succ_pos (k + q)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  obtain ⟨J, P, Q, _, _, hTor⟩ := torus_bound (k := k) (q := q) A (B + 2 * L) T (by positivity) hT
  obtain ⟨C₁, hC₁, hF⟩ := schwartz_endpoint_decay (D := Fin k → ℝ) Φ n Q hn (2 * L + m)
  obtain ⟨C₂, hC₂, hG⟩ := schwartz_endpoint_decay (D := Fin k → ℝ) Ψ n P hn 0
  refine ⟨J, l, K ^ L * C₀ * C₁ * C₂, by positivity, hInt, fun y p Z => ?_⟩
  let R := retainedMatrix k q p
  let z := p.1.1.2
  let S := 1 + ‖p.2‖
  let V := unipotentDecay l Z
  let Sy := ∑ i, |y i|
  let Sz := ∑ i, |z i|
  let U := ∑ i, y i
  let h := max (-z (Fin.last q)) 0
  let w := max (z 0) 0
  let E := A * Sy + B * Sz + T * U - (J : ℝ) * rootPos (Fin.append (m := k) (n := q + 1) y (-z))
  have hR : 0 ≤ H R := zero_le_two.trans (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos _) R)
  have hS : 0 < S := by dsimp only [S]; positivity
  have hV : 0 ≤ V := by dsimp only [V, unipotentDecay]; positivity
  obtain ⟨hCol, hFirst, hLast⟩ := retained_endpoint_norms p
  have h₁ := hF (firstRetainedColumn p) p.2 (z 0) hCol hFirst
  have h₂ := hG (lastRetainedInverseRow p) 0 (-z (Fin.last q))
    (by rw [norm_zero]; exact mul_nonneg (zero_le_one.trans hn) (norm_nonneg _)) hLast
  simp only [pow_zero, inv_one, mul_one] at h₂
  have h₀ := hZ R Z
  have hH : H R ^ L ≤ K ^ L * Real.exp ((2 * L) * Sz) * S ^ (2 * L) := by
    refine (pow_le_pow_left₀ hR (height_retained_le p) L).trans_eq ?_
    change (K * Real.exp (2 * Sz) * S ^ 2) ^ L = _
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← pow_mul S 2 L]
    congr 3
    ring
  have hTor' : E + (2 * L) * Sz - P * h - Q * w ≤ -(Sy + Sz) := by
    have hh := hTor y (-z)
    simp only [Pi.neg_apply, abs_neg, neg_neg] at hh
    dsimp only [E, h, w, Sy, Sz, U]
    linarith only [hh]
  have hHead : S ^ (2 * L) * (S ^ (2 * L + m))⁻¹ = headDecay m p.2 := by
    rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hS.ne'), one_mul]
    rfl
  have hExp : Real.exp ((2 * L) * Sz) * Real.exp (-Q * w) * Real.exp (-P * h) * Real.exp E ≤
      Real.exp (-Sy) * Real.exp (-Sz) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [hTor']
  change H R ^ M * ‖Φ (firstRetainedColumn p)‖ * ‖Ψ (lastRetainedInverseRow p)‖ *
    ‖triangularFourier k q a R Ξ Z‖ * Real.exp E ≤ _
  calc
    _ ≤ H R ^ M * (C₁ * (S ^ (2 * L + m))⁻¹ * Real.exp (-Q * w)) *
        (C₂ * Real.exp (-P * h)) * (C₀ * H R ^ l * V) * Real.exp E := by
      gcongr
    _ = (C₀ * C₁ * C₂ * V * (S ^ (2 * L + m))⁻¹ *
          Real.exp (-Q * w) * Real.exp (-P * h) * Real.exp E) * H R ^ L := by
      rw [show L = M + l from rfl, pow_add (H R) M l]
      ring
    _ ≤ (C₀ * C₁ * C₂ * V * (S ^ (2 * L + m))⁻¹ *
          Real.exp (-Q * w) * Real.exp (-P * h) * Real.exp E) *
          (K ^ L * Real.exp ((2 * L) * Sz) * S ^ (2 * L)) :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ = (K ^ L * C₀ * C₁ * C₂ * headDecay m p.2 * V) *
          (Real.exp ((2 * L) * Sz) * Real.exp (-Q * w) * Real.exp (-P * h) * Real.exp E) := by
      rw [← hHead]
      ring
    _ ≤ (K ^ L * C₀ * C₁ * C₂ * headDecay m p.2 * V) * (Real.exp (-Sy) * Real.exp (-Sz)) :=
      mul_le_mul_of_nonneg_left hExp (by unfold headDecay; positivity)
    _ = _ := by ring

end Langlands.Global.RankinSelbergGlobal.RealGapAlternateTailBound
