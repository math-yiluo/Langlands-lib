import Langlands.Global.RankinSelberg.ComplexGodementSchwartz
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof
import Langlands.Representation.Archimedean.ComplexPermutationSwap

/-! # Growth of complex standard vectors and the Godement convergence half-plane -/

noncomputable section

open MeasureTheory
open scoped SchwartzMap Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.GeneralLinear Langlands.Archimedean Langlands.LocalFactor.Archimedean
open ComplexPlaceAnalytic (complexMatrixHeight_inv two_le_complexMatrixHeight
  norm_entry_le_complexMatrixHeight)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open ArchimedeanLocal (complexNormalizedAbs)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance standardGrowthGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance standardGrowthGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

private abbrev Rect (m : ℕ) := Matrix (Fin m) (Fin (m + 1)) ℂ

private theorem norm_unitary_entry_le_one {n : ℕ} (k : unitaryCompact ℂ n) (i j : Fin n) :
    ‖k.val.val i j‖ ≤ 1 := by
  have hk := ComplexMaximalParabolicIntegration.mul_conjTranspose_one k
  have hrow : (∑ j : Fin n, ‖k.val.val i j‖ ^ 2) = 1 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i i) hk
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.mul_conj', Matrix.one_apply_eq] at h
    exact_mod_cast h
  have hs : ‖k.val.val i j‖ ^ 2 ≤ 1 := by
    rw [← hrow]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖k.val.val i j‖) (Finset.mem_univ j)
  nlinarith [norm_nonneg (k.val.val i j)]

private theorem norm_mul_unitary_entry_le {n : ℕ} (hn : 0 < n) (g : Langlands.GeneralLinear n ℂ)
    (k : unitaryCompact ℂ n) (i j : Fin n) :
    ‖(g * k.val).val i j‖ ≤ (n : ℝ) * complexMatrixHeight g := by
  change ‖∑ l : Fin n, g.val i l * k.val.val l j‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin n, complexMatrixHeight g := by
      apply Finset.sum_le_sum
      intro l _
      rw [norm_mul, ← mul_one (complexMatrixHeight g)]
      exact mul_le_mul (norm_entry_le_complexMatrixHeight hn g i l)
        (norm_unitary_entry_le_one k l j) (norm_nonneg _) ((two_le_complexMatrixHeight hn g).trans' (by norm_num))
    _ = _ := by simp [nsmul_eq_mul]

private theorem norm_unitary_mul_entry_le {n : ℕ} (hn : 0 < n) (g : Langlands.GeneralLinear n ℂ)
    (k : unitaryCompact ℂ n) (i j : Fin n) :
    ‖(k.val * g).val i j‖ ≤ (n : ℝ) * complexMatrixHeight g := by
  change ‖∑ l : Fin n, k.val.val i l * g.val l j‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin n, complexMatrixHeight g := by
      apply Finset.sum_le_sum
      intro l _
      rw [norm_mul, ← one_mul (complexMatrixHeight g)]
      exact mul_le_mul (norm_unitary_entry_le_one k i l)
        (norm_entry_le_complexMatrixHeight hn g l j) (norm_nonneg _) (by norm_num)
    _ = _ := by simp [nsmul_eq_mul]

private theorem iwasawa_diagonal_bounds {n : ℕ} (hn : 0 < n) (g : Langlands.GeneralLinear n ℂ)
    (a : Fin n → ℂˣ) (u : GeneralLinear.upperUnipotent n ℂ) (k : unitaryCompact ℂ n)
    (hg : g = Iwasawa.diagonalUnits a * u.val * k.val) (i : Fin n) :
    ‖(a i : ℂ)‖ ≤ (n : ℝ) * complexMatrixHeight g ∧
      ‖(a i : ℂ)‖⁻¹ ≤ (n : ℝ) * complexMatrixHeight g := by
  let b := Iwasawa.diagonalUnits a * u.val
  have hb : b = g * (k⁻¹ : unitaryCompact ℂ n).val := by
    rw [hg]
    change b = (b * k.val) * k.val⁻¹
    rw [mul_inv_cancel_right]
  have hbi : b⁻¹ = k.val * g⁻¹ := by
    rw [hb, mul_inv_rev]
    rfl
  have hentry : b.val i i = (a i : ℂ) := by
    change ((Iwasawa.diagonalUnits a).val * u.val.val) i i = _
    rw [Iwasawa.diagonalUnits_val, Matrix.diagonal_mul, u.2.2 i, mul_one]
  have hinv : b⁻¹.val i i = ((a i)⁻¹ : ℂˣ).val := by
    change ((Iwasawa.diagonalUnits a * u.val)⁻¹).val i i = _
    rw [mul_inv_rev, ← map_inv, Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.mul_diagonal]
    have hu : u.val⁻¹.val i i = 1 := (u⁻¹).2.2 i
    rw [hu, one_mul]
    rfl
  constructor
  · rw [← hentry, hb]
    exact norm_mul_unitary_entry_le hn g k⁻¹ i i
  · rw [← norm_inv, ← Units.val_inv_eq_inv_val, ← hinv, hbi, ← complexMatrixHeight_inv g]
    exact norm_unitary_mul_entry_le hn g⁻¹ k i i

private theorem rpow_le_natPower {x B : ℝ} (hx : 0 < x) (hB : 1 ≤ B)
    (h : x ≤ B) (hi : x⁻¹ ≤ B) (e : ℝ) : x ^ e ≤ B ^ ⌈|e|⌉₊ := by
  have hceil : |e| ≤ (⌈|e|⌉₊ : ℝ) := Nat.le_ceil _
  rw [← Real.rpow_natCast]
  by_cases he : 0 ≤ e
  · exact (Real.rpow_le_rpow hx.le h he).trans
      (Real.rpow_le_rpow_of_exponent_le hB ((le_abs_self e).trans hceil))
  · have hneg : 0 ≤ -e := neg_nonneg.mpr (le_of_not_ge he)
    calc
      x ^ e = x⁻¹ ^ (-e) := by rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv]
      _ ≤ B ^ (-e) := Real.rpow_le_rpow (inv_nonneg.mpr hx.le) hi hneg
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB ((neg_le_abs e).trans hceil)

/-- Every vector in a positive-rank complex standard module has a polynomial height bound,
with an exponent that depends only on the character list. -/
theorem exists_height_bound_standard {n : ℕ} (hn : 0 < n) (ds : List ComplexCharacterData)
    (hds : ds.length = n) :
    ∃ M : ℕ, ∀ f ∈ complexStandardModule n ds, ∃ C : ℝ,
      0 ≤ C ∧ ∀ g : Langlands.GeneralLinear n ℂ, ‖f g‖ ≤ C * complexMatrixHeight g ^ M := by
  let d (i : Fin n) := ds.get ⟨i, hds ▸ i.isLt⟩
  let q (i : Fin n) : ℂ := ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)
  let e (i : Fin n) : ℝ := 2 * ((d i).exponent + q i).re
  let M : ℕ := ∑ i, ⌈|e i|⌉₊
  refine ⟨M, fun f hf => ?_⟩
  obtain ⟨C₀, hC₀⟩ := (ComplexDuality.isCompact_unitaryCompact n).exists_bound_of_continuousOn
    hf.1.continuous.continuousOn
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C * (n : ℝ) ^ M, by positivity, fun g => ?_⟩
  obtain ⟨a, u, k, hk, hg⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  let B := (n : ℝ) * complexMatrixHeight g
  have hB : 1 ≤ B := by
    refine one_le_mul_of_one_le_of_one_le ?_ ((two_le_complexMatrixHeight hn g).trans' (by norm_num))
    exact_mod_cast hn
  have hterm (i : Fin n) :
      ‖complexPositionCharacter ds i (a i) * ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ q i‖ ≤
        B ^ ⌈|e i|⌉₊ := by
    have hi := iwasawa_diagonal_bounds hn g a u ⟨k, hk⟩ hg i
    have hpos : 0 < ‖(a i : ℂ)‖ := norm_pos_iff.mpr (a i).ne_zero
    rw [ComplexPermutation.complexPositionCharacter_eq_get ds i (by simp [hds])]
    change ‖characterWeight (d i) (q i) (a i)‖ ≤ _
    rw [norm_characterWeight, complexNormalizedAbs, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    exact rpow_le_natPower hpos hB hi.1 hi.2 (e i)
  have hχ : ‖principalSeriesCharacter ℂ n (complexPositionCharacter ds) a‖ ≤ B ^ M := by
    unfold principalSeriesCharacter
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    simp only [Complex.finrank_real_complex]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hterm i)
  have hfg : f g = principalSeriesCharacter ℂ n (complexPositionCharacter ds) a * f k :=
    hg ▸ hf.2 a u k
  have hfk : ‖f k‖ ≤ C := (hC₀ k hk).trans (le_max_left _ _)
  calc
    ‖f g‖ = ‖principalSeriesCharacter ℂ n (complexPositionCharacter ds) a‖ * ‖f k‖ := by
      rw [hfg, norm_mul]
    _ ≤ B ^ M * C := mul_le_mul hχ hfk (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [B]; rw [mul_pow]; ring

/-- For each fixed smaller standard module, the Schwartz Godement integrals of all its
vectors converge above a single explicitly parametrized threshold. -/
def ComplexGodementStandardConvergenceStatement : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (ds : List ComplexCharacterData), ds.length = m →
    ∃ M : ℕ, ∀ (d : ComplexCharacterData) (Φ : 𝓢(Rect m, ℂ))
      (f : Langlands.GeneralLinear m ℂ → ℂ), f ∈ complexStandardModule m ds →
      (m : ℝ) + M ≤ (d.exponent + ((m : ℂ) + 1) / 2).re →
      ∀ g, Integrable (godementSectionIntegrand d Φ f g) (complexGeneralLinearHaar m)

theorem complexGodementStandardConvergence : ComplexGodementStandardConvergenceStatement := by
  intro m hm ds hds
  obtain ⟨M, hM⟩ := exists_height_bound_standard hm ds hds
  refine ⟨M, fun d Φ f hf hₛ g => ?_⟩
  obtain ⟨C, _, hC⟩ := hM f hf
  refine integrable_godementSectionIntegrand_of_height_bound (C := C) d Φ hf.1.continuous ?_ hₛ g
  intro h
  simpa only [complexMatrixHeight_inv] using hC h⁻¹

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
