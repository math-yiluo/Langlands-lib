import Langlands.Global.RankinSelberg.RealGodementSection
import Langlands.Global.RankinSelberg.RealGodementHaar
import Langlands.Representation.Archimedean.PartialJacquetIntegral
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # An integrable real Godement majorant for general Schwartz tests -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg.GLDeterminantDensity
open MeasureTheory Matrix Set
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet RealJacquetFrobenius

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩

/-- The determinant weight has absolute-value exponent given by the sum of real parts. -/
theorem norm_determinantWeight_real {n : ℕ} (c : RealCharacterData) (s : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    ‖determinantWeight c s g‖ = |g.val.det| ^ (c.exponent.re + s.re) := by
  let d := determinant g
  have hp : 0 < |(d : ℝ)| := abs_pos.mpr d.ne_zero
  change ‖(c.character d : ℂ) * ((|(d : ℝ)| : ℝ) : ℂ) ^ s‖ = _
  rw [c.character_eq, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_abs, div_self hp.ne', one_pow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.norm_cpow_eq_rpow_re_of_pos hp,
    ← Real.rpow_add hp]
  rfl

private theorem absDet_eq_prod_inverse_of_iwasawa (h : G) (d : Fin m → ℝˣ)
    (u : GeneralLinear.upperUnipotent m ℝ) (k : unitaryCompact ℝ m)
    (hI : h⁻¹ = Iwasawa.diagonalUnits d * u.val * k.val) :
    |h.val.det| = ∏ i : Fin m, |(d i : ℝ)|⁻¹ := by
  have hInv : |h⁻¹.val.det| = |h.val.det|⁻¹ := by
    change |(determinant (h⁻¹) : ℝ)| = |(determinant h : ℝ)|⁻¹
    rw [map_inv, Units.val_inv_eq_inv_val, abs_inv]
  rw [← inv_inv |h.val.det|, ← hInv, hI, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
    MaximalParabolicIntegration.det_upperUnipotent, mul_one, abs_mul,
    MaximalParabolicIntegration.abs_det_unitary k, mul_one, Iwasawa.diagonalUnits_val,
    Matrix.det_diagonal, Finset.abs_prod, Finset.prod_inv_distrib]

private theorem inverse_diagonal_of_iwasawa (h : G) (d : Fin m → ℝˣ)
    (u : GeneralLinear.upperUnipotent m ℝ) (k : unitaryCompact ℝ m)
    (hI : h⁻¹ = Iwasawa.diagonalUnits d * u.val * k.val) (i : Fin m) :
    |(d i : ℝ)|⁻¹ = ‖(k.val.val * h.val) i i‖ := by
  let b : G := Iwasawa.diagonalUnits d * u.val
  have hB : b⁻¹ = k.val * h := by
    have hh : h = k.val⁻¹ * b⁻¹ := by
      rw [← _root_.mul_inv_rev, show b * k.val = h⁻¹ from hI.symm, inv_inv]
    rw [hh, ← mul_assoc, mul_inv_cancel, one_mul]
  have hVal : (k.val.val * h.val) i i = ((d i : ℝ))⁻¹ := by
    rw [← Units.val_mul, ← hB]
    change ((Iwasawa.diagonalUnits d * u.val)⁻¹ : G).val i i = _
    rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.mul_diagonal]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, ← Subgroup.coe_inv]
    change (u⁻¹ : GeneralLinear.upperUnipotent m ℝ).val.val i i * (d i : ℝ)⁻¹ = _
    rw [(u⁻¹).property.2 i, one_mul]
  rw [hVal, Real.norm_eq_abs, abs_inv]

private theorem exists_compact_diagonal_bound (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (h : Langlands.GeneralLinear m ℝ) (d : Fin m → ℝˣ)
      (u : GeneralLinear.upperUnipotent m ℝ) (k : unitaryCompact ℝ m),
      h⁻¹ = Iwasawa.diagonalUnits d * u.val * k.val → ∀ i,
      |(d i : ℝ)|⁻¹ ≤ B * (1 + ‖h.val‖) := by
  have hK : Continuous (fun k : unitaryCompact ℝ m => k.val.val) := Units.continuous_val.comp continuous_subtype_val
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
  classical
  let L : Fin m → Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ := fun i => entryCLM i i
  let D : ℝ≥0 := Finset.univ.sup fun i : Fin m => ‖L i‖₊
  let B : ℝ := max (D : ℝ) 1 * max A 1
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (le_max_right _ _)
  refine ⟨B, hB, fun h d u k hI i => ?_⟩
  rw [inverse_diagonal_of_iwasawa h d u k hI i]
  have hNorm : ‖L i‖ ≤ max (D : ℝ) 1 := by
    apply le_trans _ (le_max_left _ _)
    exact_mod_cast Finset.le_sup (f := fun j : Fin m => ‖L j‖₊) (Finset.mem_univ i)
  have hkn : ‖k.val.val‖ ≤ max A 1 := (hA k (mem_univ _)).trans (le_max_left _ _)
  change ‖L i (k.val.val * h.val)‖ ≤ _
  calc
    _ ≤ ‖L i‖ * ‖k.val.val * h.val‖ := (L i).le_opNorm _
    _ ≤ max (D : ℝ) 1 * (max A 1 * ‖h.val‖) := by
      gcongr
      exact (Matrix.linfty_opNorm_mul k.val.val h.val).trans (mul_le_mul_of_nonneg_right hkn (norm_nonneg h.val))
    _ = B * ‖h.val‖ := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (zero_le_one.trans hB)

/-- When the real part of the leading exponent is sufficiently large, dividing the
weighted norm by the determinant factor in matrix Haar gives polynomial growth
in the matrix entries alone. -/
theorem exists_weightedLower_bound (c : RealCharacterData) (ds : List RealBlock) {f : G → ℂ}
    (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (hc : ∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2) :
    ∃ (N : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ h : G,
      ‖f h⁻¹‖ * ‖determinantWeight c (((m : ℂ) + 1) / 2) h‖ ≤
        B * (|h.val.det| ^ m * (1 + ‖h.val‖) ^ N) := by
  let σ := normExponent (realPositionExponent ds) m
  let s : ℝ := c.exponent.re + ((m : ℝ) + 1) / 2
  let γ : Fin m → ℝ := fun i => s - (m : ℝ) - σ i
  have hγ (i : Fin m) : 0 ≤ γ i := by
    have h := hc i
    change (m : ℝ) + σ i ≤ s at h
    dsimp only [γ]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (∑ i : Fin m, γ i)
  obtain ⟨A, hA⟩ := exists_bound_unitaryCompact hf.1.continuous
  have hA₀ : 0 ≤ A := (norm_nonneg _).trans (hA 1 (unitaryCompact ℝ m).one_mem)
  obtain ⟨D, hD, hDiag⟩ := exists_compact_diagonal_bound m
  refine ⟨N, A * D ^ N, mul_nonneg hA₀ (pow_nonneg (zero_le_one.trans hD) _), ?_⟩
  intro h
  obtain ⟨d, u, k, hk, hI⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact h⁻¹
  let q := fun i : Fin m => |(d i : ℝ)|⁻¹
  have hq (i : Fin m) : 0 < q i := inv_pos.mpr (abs_pos.mpr (d i).ne_zero)
  have hDet : |h.val.det| = ∏ i : Fin m, q i := absDet_eq_prod_inverse_of_iwasawa h d u ⟨k, hk⟩ hI
  have hF : ‖f h⁻¹‖ ≤ A * ∏ i : Fin m, q i ^ (-σ i) := by
    rw [hI, hf.2, norm_mul, norm_principalSeriesCharacter (RealStrictCharacterLanglandsQuotient.isSignedPower ds)]
    rw [mul_comm A]
    simp only [q, ← Real.rpow_neg_eq_inv_rpow, neg_neg]
    exact mul_le_mul_of_nonneg_left (hA k hk)
      (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (d i : ℝ)) (σ i))
  have hS : (((m : ℂ) + 1) / 2).re = ((m : ℝ) + 1) / 2 := by norm_num [Complex.div_re]
  have hWeight : ‖determinantWeight c (((m : ℂ) + 1) / 2) h‖ = |h.val.det| ^ s := by
    rw [norm_determinantWeight_real, hS]
  have hCoeff : (∏ i : Fin m, q i ^ (-σ i)) * |h.val.det| ^ s =
      |h.val.det| ^ m * ∏ i : Fin m, q i ^ γ i := by
    rw [← Real.rpow_natCast, hDet, ← Real.finsetProd_rpow _ _ (fun i _ => (hq i).le) s,
      ← Real.finsetProd_rpow _ _ (fun i _ => (hq i).le) (m : ℝ),
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_add (hq i), ← Real.rpow_add (hq i)]
    congr 1
    dsimp only [γ]
    ring
  let B := D * (1 + ‖h.val‖)
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hD (le_add_of_nonneg_right (norm_nonneg h.val))
  have hProd : (∏ i : Fin m, q i ^ γ i) ≤ D ^ N * (1 + ‖h.val‖) ^ N := by
    calc
      _ ≤ ∏ i : Fin m, B ^ γ i := Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (hq i).le _)
        fun i _ => Real.rpow_le_rpow (hq i).le (hDiag h d u ⟨k, hk⟩ hI i) (hγ i)
      _ = B ^ (∑ i : Fin m, γ i) := (Real.rpow_sum_of_nonneg (zero_le_one.trans hB) (fun i _ => hγ i)).symm
      _ ≤ B ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hB hN
      _ = _ := by rw [Real.rpow_natCast, mul_pow]
  rw [hWeight]
  calc
    _ ≤ (A * ∏ i : Fin m, q i ^ (-σ i)) * |h.val.det| ^ s :=
      mul_le_mul_of_nonneg_right hF (Real.rpow_nonneg (abs_nonneg _) _)
    _ = A * (|h.val.det| ^ m * ∏ i : Fin m, q i ^ γ i) := by rw [mul_assoc, hCoeff]
    _ ≤ A * (|h.val.det| ^ m * (D ^ N * (1 + ‖h.val‖) ^ N)) := by gcongr
    _ = _ := by ring

private def lastRowsRightInverse (g : H) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  g⁻¹.val.submatrix id Fin.succ

private theorem continuous_lastRowsRightInverse : Continuous (lastRowsRightInverse (m := m)) :=
  continuous_matrix fun i j => Units.continuous_coe_inv.matrix_elem i j.succ

private theorem rowPoint_mul_lastRowsRightInverse (g : H) (h : M) :
    rowPoint h g * lastRowsRightInverse g = h := by
  have hI : lastRows g.val * lastRowsRightInverse g = (1 : M) := by
    ext i j
    change (g.val * g⁻¹.val) i.succ j.succ = _
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [Matrix.one_apply, Fin.succ_inj]
  rw [rowPoint, Matrix.mul_assoc, hI, Matrix.mul_one]

/-- All Schwartz derivatives have arbitrary polynomial decay in the lower matrix,
uniformly for upper translates in a compact set. -/
theorem exists_uniform_schwartz_decay {T : Set H} (hT : IsCompact T) (Φ : 𝓢(X, ℂ)) (N k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ T, ∀ h : G,
      ‖iteratedFDeriv ℝ k Φ (rowPoint h.val g)‖ ≤ B * ((1 + ‖h.val‖) ^ N)⁻¹ := by
  obtain ⟨D₀, hD₀⟩ := hT.exists_bound_of_continuousOn continuous_lastRowsRightInverse.continuousOn
  let D := max D₀ 1
  have hD : 1 ≤ D := le_max_right _ _
  let S := (2 : ℝ) ^ N * (Finset.Iic (N, k)).sup
    (fun q : ℕ × ℕ => SchwartzMap.seminorm ℝ q.1 q.2) Φ
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  refine ⟨D ^ N * S, mul_nonneg (pow_nonneg (zero_le_one.trans hD) _) hS, ?_⟩
  intro g hg h
  have hRecover : ‖h.val‖ ≤ ‖rowPoint h.val g‖ * D := by
    conv_lhs => rw [← rowPoint_mul_lastRowsRightInverse g h.val]
    exact (Matrix.linfty_opNorm_mul (rowPoint h.val g) (lastRowsRightInverse g)).trans (mul_le_mul_of_nonneg_left
      ((hD₀ g hg).trans (le_max_left _ _)) (norm_nonneg (rowPoint h.val g)))
  have hBase : 1 + ‖h.val‖ ≤ D * (1 + ‖rowPoint h.val g‖) := by
    rw [mul_add, mul_one, mul_comm D ‖rowPoint h.val g‖]
    exact add_le_add hD hRecover
  have hDecay : (1 + ‖rowPoint h.val g‖) ^ N * ‖iteratedFDeriv ℝ k Φ (rowPoint h.val g)‖ ≤ S :=
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (N, k)) (𝕜 := ℝ) le_rfl le_rfl Φ (rowPoint h.val g)
  have hP : 0 < (1 + ‖h.val‖) ^ N := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hP, mul_comm ‖iteratedFDeriv ℝ k Φ _‖]
  calc
    _ ≤ (D * (1 + ‖rowPoint h.val g‖)) ^ N *
        ‖iteratedFDeriv ℝ k Φ (rowPoint h.val g)‖ := by gcongr
    _ ≤ D ^ N * S := by
      rw [mul_pow, mul_assoc]
      exact mul_le_mul_of_nonneg_left hDecay (by positivity)

/-- Sufficient matrix decay times the forward determinant density is integrable on real Haar. -/
theorem exists_integrable_matrixDecay (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ L : ℕ, Integrable (fun h : G => |h.val.det| ^ m * ((1 + ‖h.val‖) ^ L)⁻¹) μ := by
  let ν := realMatrixVolume m
  let : ν.IsAddHaarMeasure := by unfold ν realMatrixVolume; infer_instance
  obtain ⟨e, he, hμ⟩ := exists_realMatrixHaar_eq_smul μ
  let L := ν.integrablePower
  let b : M → ℝ := fun h => ((1 + ‖h‖) ^ L)⁻¹
  have hb : Integrable b ν := (ν.integrable_pow_neg_integrablePower).congr
    (Filter.Eventually.of_forall fun h => by
      simp only [b, L, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖h‖), Real.rpow_natCast])
  unfold realMatrixHaar at hμ
  have h := (integrable_forwardWeight_iff_of_eq_smul (K := ℝ) (E := ℝ) m
    nnnormHom continuous_nnnorm ν μ e he hμ b).2 hb.integrableOn
  exact ⟨L, by simpa only [forwardWeight, NNReal.smul_def, smul_eq_mul, NNReal.coe_pow,
    nnnormHom_apply, coe_nnnorm, Real.norm_eq_abs, b] using h⟩

/-- General Schwartz tests have a common integrable lower-group majorant over
every compact set of upper translates on a right half-plane of the leading exponent. -/
def RealGodementSchwartzMajorantStatement : Prop :=
  ∀ (m : ℕ) (μ : Measure (Langlands.GeneralLinear m ℝ)) [μ.IsHaarMeasure]
    (c : RealCharacterData) (ds : List RealBlock) (f : Langlands.GeneralLinear m ℝ → ℂ),
    f ∈ principalSeries ℝ m (realPositionCharacter ds) →
    (∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤ c.exponent.re + ((m : ℝ) + 1) / 2) →
    ∀ (Φ : 𝓢(Matrix (Fin m) (Fin (m + 1)) ℝ, ℂ)) (T : Set (Langlands.GeneralLinear (m + 1) ℝ)),
    IsCompact T →
    ∃ b : Langlands.GeneralLinear m ℝ → ℝ, Integrable b μ ∧
      ∀ g ∈ T, ∀ h : Langlands.GeneralLinear m ℝ,
        ‖f h⁻¹‖ * ‖determinantWeight c (((m : ℂ) + 1) / 2) h‖ * ‖Φ (rowPoint h.val g)‖ ≤ b h

theorem realGodementSchwartzMajorant : RealGodementSchwartzMajorantStatement := by
  intro m μ _ c ds f hf hc Φ T hT
  obtain ⟨N, A, hA, hN⟩ := exists_weightedLower_bound c ds hf hc
  obtain ⟨L, hL⟩ := exists_integrable_matrixDecay μ
  obtain ⟨B, hB, hΦ⟩ := exists_uniform_schwartz_decay hT Φ (N + L) 0
  simp only [norm_iteratedFDeriv_zero] at hΦ
  refine ⟨fun h => (A * B) * (|h.val.det| ^ m * ((1 + ‖h.val‖) ^ L)⁻¹), hL.const_mul _, ?_⟩
  intro g hg h
  have hp : (1 + ‖h.val‖) ^ N ≠ 0 := by positivity
  calc
    _ ≤ (A * (|h.val.det| ^ m * (1 + ‖h.val‖) ^ N)) * (B * ((1 + ‖h.val‖) ^ (N + L))⁻¹) :=
      mul_le_mul (hN h) (hΦ g hg h) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add, _root_.mul_inv_rev]; field_simp

end Langlands.Global.RankinSelbergGlobal.RealGodement
