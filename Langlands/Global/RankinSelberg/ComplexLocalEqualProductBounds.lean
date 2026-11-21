import Langlands.Global.RankinSelberg.ComplexLocalEqualShiftedTorus
import Langlands.Global.RankinSelberg.ComplexLocalIwasawaLogBounds
import Langlands.Representation.Archimedean.ComplexSwapJacquetDecay

/-! # Shifted toral majorants of the equal-rank double kernel -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal ComplexLocalIwasawa
open ComplexLocalWhittakerGauge (logTorus)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)
open RealConvergenceAnalysis (rootPos)

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "Y" => Fin m → ℝ
local notation "Z" => Fin n → ℝ
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ m
local notation "K'" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "pad" => padGL (R := ℂ) (Nat.le_succ m)
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

/-- Logarithmic coordinates in the larger Iwasawa decomposition, with the smaller
unitary factor included on the left. -/
def equalProductAlpha (k : K) (g : G) : Z :=
  alpha (pad k.val * g)

private theorem exp_alpha_det (k : K') (g : G) :
    complexNormalizedAbs g.val.det = Real.exp (2 * ∑ j, alpha (k.val * g) j) := by
  rw [← complexNormalizedAbs_det_eq_exp_alpha]
  simp only [complexNormalizedAbs, Units.val_mul, Matrix.det_mul, norm_mul,
    Langlands.Archimedean.ComplexBlockParabolicProof.normSq_det_unitary k.2, one_mul]

private theorem norm_detPower_unitary_left (k : K') (g : G) (s : ℂ) :
    ‖P g s‖ = Real.exp (2 * s.re * ∑ j, alpha (k.val * g) j) := by
  rw [ArchimedeanLocal.detPower, RealConvergenceAnalysis.norm_cexp_mul_ofReal,
    exp_alpha_det k, Real.log_exp]
  congr 1
  ring

private theorem norm_detCharacter_eq_exp (d : ComplexCharacterData) (k : K') (g : G) :
    ‖(d.character (determinant g) : ℂ)‖ = Real.exp (2 * d.exponent.re * ∑ j, alpha (k.val * g) j) := by
  have h : ‖(d.character (determinant g) : ℂ)‖ = complexNormalizedAbs g.val.det ^ d.exponent.re := by
    rw [ComplexSwapJacquet.norm_character]
    change ‖g.val.det‖ ^ (2 * d.exponent.re) = (‖g.val.det‖ ^ (2 : ℕ)) ^ d.exponent.re
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
  rw [h, exp_alpha_det k, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

private theorem abs_coordinate_le_sum {j : ℕ} (z : Fin j → ℝ) (i : Fin j) :
    |z i| ≤ ∑ t, |z t| :=
  Finset.single_le_sum (f := fun t => |z t|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

private theorem sum_abs_shift_le (x : Y) (z : Z) :
    (∑ i, |x i|) ≤ (∑ i, |(x + equalTorusShift z) i|) + 2 * (n : ℝ) * ∑ j, |z j| := by
  have h (i : Fin m) : |x i| ≤ |(x + equalTorusShift z) i| + 2 * ∑ j, |z j| := by
    let u := x i + (z i.castSucc - z (Fin.last m))
    change |x i| ≤ |u| + _
    rw [show x i = u - (z i.castSucc - z (Fin.last m)) by dsimp [u]; ring]
    have hi := (abs_sub (z i.castSucc) (z (Fin.last m))).trans
      (add_le_add (abs_coordinate_le_sum z i.castSucc) (abs_coordinate_le_sum z (Fin.last m)))
    exact (abs_sub _ _).trans (add_le_add le_rfl (hi.trans_eq (by ring)))
  refine (Finset.sum_le_sum fun i _ => h i).trans ?_
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hS : 0 ≤ ∑ j, |z j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith

private theorem sum_abs_pad_shift_le (x : Y) (z : Z) :
    (∑ j, |(padTorusLog x + z) j|) ≤
      (∑ i, |(x + equalTorusShift z) i|) + (n : ℝ) * ∑ j, |z j| := by
  rw [padTorusLog_add_eq_shifted x z]
  refine (Finset.sum_le_sum fun _ _ => abs_add_le _ _).trans ?_
  rw [Finset.sum_add_distrib]
  have hpad : (∑ j, |padTorusLog (x + equalTorusShift z) j|) =
      ∑ i, |(x + equalTorusShift z) i| := by
    rw [Fin.sum_univ_castSucc]
    simp
  rw [hpad, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one]
  have hN : 0 ≤ (n : ℝ) := by positivity
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (abs_coordinate_le_sum z (Fin.last m)) hN)

private theorem sum_abs_eq_sum_pos_sub (z : Z) :
    (∑ j, |z j|) = 2 * (∑ j, max (z j) 0) - ∑ j, z j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases le_total 0 (z j) with h | h
  · rw [max_eq_left h, abs_of_nonneg h]
    ring
  · rw [max_eq_right h, abs_of_nonpos h]
    ring

private theorem exp_growth_bounds (z : Z) {L B t : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hZ : ∀ i, z i ≤ L) {J : ℕ} (hJ : 2 * B * (n : ℝ) + t * (n : ℝ) ≤ J) :
    B * (∑ i, |z i|) + t * (n : ℝ) * z (Fin.last m) ≤
      (J : ℝ) * L - B * ∑ i, z i := by
  rw [sum_abs_eq_sum_pos_sub]
  have hS : (∑ i, max (z i) 0) ≤ (n : ℝ) * L :=
    (Finset.sum_le_sum (fun i _ => max_le (hZ i) hL)).trans_eq
      (by simp [nsmul_eq_mul])
  have h₁ := mul_le_mul_of_nonneg_left hS hB
  have h₂ := mul_le_mul_of_nonneg_left (hZ (Fin.last m)) (mul_nonneg ht (by positivity : 0 ≤ (n : ℝ)))
  have h₃ := mul_le_mul_of_nonneg_right hJ hL
  linarith

private theorem norm_large_on_padded_torus
    {a : ℂˣ} {es : List ComplexCharacterData} (V : complexWhittakerModel (r + 1) es a)
    (x : Y) (k : K) (g : G) :
    ‖V.val (pad (logTorus x * k.val) * g)‖ =
      ‖V.val (logTorus (padTorusLog x + equalProductAlpha k g) * (kpart (pad k.val * g)).val)‖ := by
  let v := conjTorus (padTorusLog x) (npart (pad k.val * g))
  rw [map_mul, pad_logTorus, mul_assoc, torus_mul_eq, mul_assoc,
    complexWhittakerModel_left_equivariant V.2 v.val v.2, norm_mul]
  simp only [complexWhittakerCharacter, HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex,
    one_mul, equalProductAlpha]

/-- A shifted exponential majorant for the equal-rank product kernel. Only positive
matrix norm powers depend on the spectral parameter. -/
theorem exists_equalProductBounds (L : Y →L[ℝ] ℝ) (a : ℂˣ) (ds es : List ComplexCharacterData)
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a)) :
    ∃ (B : ℝ), 0 ≤ B ∧ ∃ σ : ℝ, ∀ d : ComplexCharacterData, ∀ s : ℂ, σ < s.re →
      ∃ (C : ℝ) (J : ℕ), 0 ≤ C ∧ ∀ (Φ : Mat → ℂ) (x : Y) (k : K) (g : G),
        Real.exp (L x) *
          ‖Φ g.val * (d.character (determinant g) : ℂ) * P g (s + ((m : ℕ) : ℂ) / 2) *
            (U.val (logTorus x * k.val) * V.val (pad (logTorus x * k.val) * g) *
              P (logTorus x * k.val) (s - 1 / 2))‖ ≤
        C * Real.exp (-(∑ j, |(x + equalTorusShift (equalProductAlpha k g)) j|)) *
          (max 1 ‖g.val‖ ^ J * ‖Φ g.val‖ *
            complexNormalizedAbs g.val.det ^ (d.exponent.re + ((n : ℝ) - B) / 2)) := by
  obtain ⟨Nu, hNu⟩ := complexWhittakerSimpleRootMajorization r ds a U
  obtain ⟨Nv, hNv⟩ := complexWhittakerSimpleRootMajorization (r + 1) es (-a) V
  obtain ⟨Cu, hCu, hU⟩ := hNu 0 []
  obtain ⟨D, hD, hDopt⟩ := @exists_exp_alpha_unitary_mul_le n
  let A := (Nu : ℝ) + ‖L‖ + (Nv : ℝ)
  let B := (2 * ((Nu : ℝ) + ‖L‖) + (Nv : ℝ)) * (n : ℝ)
  refine ⟨B, by dsimp only [B]; positivity, ((A + 1) * (n : ℝ) + 1) / 2, ?_⟩
  intro d s hs
  let t := 2 * (s.re - 1 / 2)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hT : (A + 1) * (n : ℝ) ≤ t := by dsimp only [t]; linarith
  have ht : 0 ≤ t := (by positivity : 0 ≤ (A + 1) * (n : ℝ)).trans hT
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨M, hM⟩ := exists_paddedTorus_decay A hA t hT
  obtain ⟨Cv, hCv, hV⟩ := hNv M []
  obtain ⟨J, hJ⟩ := exists_nat_ge (2 * B * (n : ℝ) + t * (n : ℝ))
  let C := Cu * Cv * D ^ J
  refine ⟨C, J, by dsimp only [C]; positivity, fun Φ x k g => ?_⟩
  let k₀ : K' := ⟨pad k.val, unitary_padGL (Nat.le_succ m) k.val k.2⟩
  let z := equalProductAlpha k g
  let y := x + equalTorusShift z
  let S := fun u : Y => ∑ j, |u j|
  let S' := fun u : Z => ∑ j, |u j|
  let R := max 1 ‖g.val‖
  let l := Real.log (D * R)
  have hR : 1 ≤ R := le_max_left _ _
  have hDR : 1 ≤ D * R := one_le_mul_of_one_le_of_one_le hD hR
  have hDR0 : 0 < D * R := zero_lt_one.trans_le hDR
  have hl : 0 ≤ l := Real.log_nonneg hDR
  have hz (i : Fin n) : z i ≤ l := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hDR0]
    exact (hDopt k₀ g i).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (zero_le_one.trans hD))
  have hnorm : ‖x‖ ≤ S x := by
    apply (pi_norm_le_iff_of_nonneg (by dsimp [S]; positivity)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using abs_coordinate_le_sum x i
  have hL : L x ≤ ‖L‖ * S x :=
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ L.le_opNorm x).trans
      (mul_le_mul_of_nonneg_left hnorm (norm_nonneg L)))
  have hX : S x ≤ S y + 2 * (n : ℝ) * S' z := sum_abs_shift_le x z
  have hY : S' (padTorusLog x + z) ≤ S y + (n : ℝ) * S' z := sum_abs_pad_shift_le x z
  have hRoot : rootPos (padTorusLog x + z) = rootPos (padTorusLog y) := by
    rw [padTorusLog_add_eq_shifted, rootPos_add_const]
  have hU₀ : ‖U.val (logTorus x * k.val)‖ ≤ Cu * Real.exp ((Nu : ℝ) * S x) := by
    simpa only [S, List.map_nil, List.prod_nil, Module.End.one_apply, Nat.cast_zero, zero_mul,
      sub_zero] using hU x k
  have hV₀ : ‖V.val (pad (logTorus x * k.val) * g)‖ ≤
      Cv * Real.exp ((Nv : ℝ) * S' (padTorusLog x + z) - (M : ℝ) * rootPos (padTorusLog y)) := by
    rw [norm_large_on_padded_torus, ← hRoot]
    simpa only [rootPos, S', z, List.map_nil, List.prod_nil, Module.End.one_apply] using
      hV (padTorusLog x + z) (kpart (pad k.val * g))
  have hxPow : ‖P (logTorus x * k.val) (s - 1 / 2)‖ = Real.exp (t * ∑ j, x j) := by
    rw [norm_detPower_logTorus_mul]
    simp only [t, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  have hgPow : ‖P g (s + ((m : ℕ) : ℂ) / 2)‖ =
      Real.exp (2 * (s.re + (m : ℝ) / 2) * ∑ j, z j) := by
    rw [norm_detPower_unitary_left k₀]
    simp only [z, equalProductAlpha, k₀, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re,
      Nat.cast_add, Nat.cast_one, Complex.one_re]
  have hχ : ‖(d.character (determinant g) : ℂ)‖ =
      Real.exp (2 * d.exponent.re * ∑ j, z j) := norm_detCharacter_eq_exp d k₀ g
  let T := L x + (Nu : ℝ) * S x + (Nv : ℝ) * S' (padTorusLog x + z) -
    (M : ℝ) * rootPos (padTorusLog y) + t * (∑ j, x j) +
    2 * (s.re + (m : ℝ) / 2) * (∑ j, z j) + 2 * d.exponent.re * ∑ j, z j
  have hT' : T ≤ -S y + (J : ℝ) * l + (2 * d.exponent.re + (n : ℝ) - B) * ∑ j, z j := by
    have hx := mul_le_mul_of_nonneg_left hX (by positivity : 0 ≤ (Nu : ℝ) + ‖L‖)
    have hy := mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg Nv : 0 ≤ (Nv : ℝ))
    have hs' : t * (∑ j, x j) + 2 * (s.re + (m : ℝ) / 2) * (∑ j, z j) =
        t * (∑ j, y j) + (n : ℝ) * (∑ j, z j) + t * (n : ℝ) * z (Fin.last m) := by
      dsimp only [t, y]
      nlinarith only [equalDeterminantLog_shifted x z s.re]
    have hGrowth := exp_growth_bounds z hl hB ht hz hJ
    have hDecay := hM y
    dsimp only [T, A, B, S, S'] at hx hy hL hGrowth hDecay ⊢
    linarith
  have hpart : Real.exp ((2 * d.exponent.re + (n : ℝ) - B) * ∑ j, z j) =
      complexNormalizedAbs g.val.det ^ (d.exponent.re + ((n : ℝ) - B) / 2) := by
    rw [exp_alpha_det k₀, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    change Real.exp _ = Real.exp ((2 * ∑ j, z j) * _)
    congr 1
    ring
  simp only [norm_mul, hχ, hgPow, hxPow]
  calc
    _ ≤ Real.exp (L x) *
        (‖Φ g.val‖ * Real.exp (2 * d.exponent.re * ∑ j, z j) *
          Real.exp (2 * (s.re + (m : ℝ) / 2) * ∑ j, z j) *
          ((Cu * Real.exp ((Nu : ℝ) * S x)) *
            (Cv * Real.exp ((Nv : ℝ) * S' (padTorusLog x + z) -
              (M : ℝ) * rootPos (padTorusLog y))) * Real.exp (t * ∑ j, x j))) := by
      gcongr
    _ = Cu * Cv * ‖Φ g.val‖ * Real.exp T := by
      dsimp only [T]
      simp only [Real.exp_add, Real.exp_sub]
      ring
    _ ≤ Cu * Cv * ‖Φ g.val‖ *
        Real.exp (-S y + (J : ℝ) * l + (2 * d.exponent.re + (n : ℝ) - B) * ∑ j, z j) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hT') (by positivity)
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, hpart, Real.exp_nat_mul, Real.exp_log hDR0, mul_pow]
      dsimp only [S, C]
      ring

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
