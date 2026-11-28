import Langlands.Global.RankinSelberg.RealCompactDiracBigCell
import Langlands.Global.RankinSelberg.RealStandardCompactDirac

/-!
# Proof of the quantitative compact Dirac limit for real scalar principal series

`realStandardCompactDirac` proves `RealStandardCompactDiracStatement`. The seed is the
extension of the corner-minor profile `φ₀ = ∏ₗ (Δₗ Δₗ₊₁)^{p l} (∏ₗ Δₗ)^{2m}`, the torus elements
are `a_t = diag(t^{n-1}, …, 1)` and the scalars are `b_t = (c_t ∫ W)⁻¹`. The error is
`C t⁻¹ (‖ψ‖ + L)`, so `δ = 1`.
-/

noncomputable section

open Matrix Filter Topology MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactDirac

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open RealStandardCompactBanach RealPrincipalSeriesHilbert RealCompactDirac
open PrincipalSeriesExtension

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

/-! ## Sign compatibility -/

theorem isSignCovariant_of_isSignCompatible {ds : List RealBlock} {ψ : C(O, ℂ)}
    (hψ : IsSignCompatible ds ψ) : IsSignCovariant (realPositionCharacter ds) ψ := by
  intro d κ
  let ε : Fin n → ℤˣ := fun i => if 0 < (d i : ℝ) then 1 else -1
  have hsm : signMatrix ε = signDiagonal (fun i => (d i : ℝ)) := by
    apply Subtype.ext
    rw [signMatrix_val]
    change _ = Matrix.diagonal fun i => GramFormula.signReal (d i : ℝ)
    congr 1
    funext i
    simp only [ε, GramFormula.signReal, coe_signUnit]
    split_ifs <;> simp
  have hsc : signCharacter ds ε =
      ∏ i : Fin n, realPositionCharacter ds (i : ℕ) (GramFormula.signUnit (d i)) := by
    unfold signCharacter
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    apply Units.ext
    simp only [ε, GramFormula.signUnit, coe_signUnit]
    split_ifs <;> simp
  rw [← hsm, hψ ε κ, hsc]

/-! ## The torus elements and the scalars -/

theorem unitHeight_scale_le {t : ℝ} (ht : 1 ≤ t) :
    unitHeight (A := Mat) (Iwasawa.diagonalUnits (scaleUnits n t)) ≤ t ^ (n - 1) := by
  have h1 : (1 : ℝ) ≤ t ^ (n - 1) := one_le_pow₀ ht
  have hτ : ∀ i : Fin n, ((scaleUnits n t i : ℝˣ) : ℝ) = t ^ (n - 1 - (i : ℕ)) := fun i => by
    rw [scaleUnits_val, max_eq_left ht]
  refine max_le h1 (max_le ?_ ?_)
  · rw [Iwasawa.diagonalUnits_val, Matrix.linfty_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs, hτ, abs_of_pos (by positivity)]
    exact pow_le_pow_right₀ ht (Nat.sub_le _ _)
  · rw [← map_inv, Iwasawa.diagonalUnits_val, Matrix.linfty_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs, Pi.inv_apply, Units.val_inv_eq_inv_val, hτ,
      abs_of_pos (by positivity)]
    exact (inv_le_one_of_one_le₀ (one_le_pow₀ ht)).trans h1

theorem norm_scaleFactor_pos (s : Fin n → ℂ) (t : ℝ) : 0 < ‖scaleFactor s t‖ := by
  rw [scaleFactor, norm_prod]
  refine Finset.prod_pos fun l _ => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.2 (scaleUnits_pos t l))]
  exact Real.rpow_pos_of_pos (inv_pos.2 (scaleUnits_pos t l)) _

theorem norm_scaleFactor_inv_le (s : Fin n → ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖scaleFactor s t‖⁻¹ ≤ t ^ ⌈((n - 1 : ℕ) : ℝ) * growthExponent s⌉₊ := by
  have hM1 : (1 : ℝ) ≤ t ^ (n - 1) := one_le_pow₀ ht
  have hM0 : 0 < t ^ (n - 1) := by linarith
  have hτ : ∀ i : Fin n, ((scaleUnits n t i : ℝˣ) : ℝ) = t ^ (n - 1 - (i : ℕ)) := fun i => by
    rw [scaleUnits_val, max_eq_left ht]
  rw [scaleFactor, norm_prod, ← Finset.prod_inv_distrib]
  calc ∏ l : Fin n, ‖(((((scaleUnits n t l : ℝˣ) : ℝ)⁻¹ : ℝ) : ℂ)) ^ s l‖⁻¹
      ≤ ∏ l : Fin n, (t ^ (n - 1)) ^ |(s l).re| := by
        gcongr with l _
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.2 (scaleUnits_pos t l)),
          Real.inv_rpow (scaleUnits_pos t l).le, inv_inv]
        refine rpow_le_of_le_of_inv_le (scaleUnits_pos t l) ?_ ?_
        · rw [hτ]
          exact pow_le_pow_right₀ ht (Nat.sub_le _ _)
        · rw [hτ]
          exact (inv_le_one_of_one_le₀ (one_le_pow₀ ht)).trans hM1
    _ = (t ^ (n - 1)) ^ growthExponent s := by
        rw [growthExponent, Real.rpow_sum_of_pos hM0]
    _ = t ^ (((n - 1 : ℕ) : ℝ) * growthExponent s) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    _ ≤ t ^ (⌈((n - 1 : ℕ) : ℝ) * growthExponent s⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht (Nat.le_ceil _)
    _ = t ^ ⌈((n - 1 : ℕ) : ℝ) * growthExponent s⌉₊ := Real.rpow_natCast _ _

/-! ## The proof -/

/-- **Quantitative compact Dirac limit** for the real scalar principal series. -/
theorem realStandardCompactDirac : RealStandardCompactDiracStatement := by
  intro r cs _hcs
  set ds := cs.map RealBlock.character with hds
  set χ := realPositionCharacter ds with hχdef
  set e := GramFormula.realPositionExponent ds with hedef
  have hχ : PartialJacquet.IsSignedPower χ e := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  obtain ⟨p, hp⟩ := RealStrictCharacterLanglandsQuotient.exists_signs ds
  set s := dualExponent (r + 1) e with hsdef
  set q := growthExponent s with hqdef
  have hq0 : 0 ≤ q := growthExponent_nonneg s
  obtain ⟨M₀, hM₀⟩ := exists_re_integral_weight_pos (n := r + 1) p s
  set m := max M₀ (⌈1 + (((r + 1 : ℕ) : ℝ) + 2) * q⌉₊ + 1) with hmdef
  have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 _) (le_max_right _ _)
  have hmq : 1 + (((r + 1 : ℕ) : ℝ) + 2) * q ≤ 2 * m := by
    have h1 := Nat.le_ceil (1 + (((r + 1 : ℕ) : ℝ) + 2) * q)
    have h2 := (Nat.cast_le (α := ℝ)).2
      (le_max_right M₀ (⌈1 + (((r + 1 : ℕ) : ℝ) + 2) * q⌉₊ + 1))
    rw [Nat.cast_add, Nat.cast_one, ← hmdef] at h2
    have h3 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  set I : ℂ := ∫ κ, weight p m s κ ∂haarOrthogonal (r + 1) with hIdef
  have hIre : 0 < I.re := hM₀ m (le_max_left _ _)
  have hI : I ≠ 0 := fun h => by rw [h, Complex.zero_re] at hIre; exact lt_irrefl 0 hIre
  have hInorm : 0 < ‖I‖ := norm_pos_iff.2 hI
  obtain ⟨K, hK0, hK⟩ := exists_pointwise_error hχ.one hp s hm1 hmq
  have hmem := seedVector_mem (n := r + 1) hχ hp m
  have hps : seedVector (n := r + 1) p m e ∈ principalSeries ℝ (r + 1) χ :=
    (Submodule.mem_inf.1 hmem).1
  have hK' : seedVector (n := r + 1) p m e ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℝ))
        (unitaryCompact ℝ (r + 1)) := (Submodule.mem_inf.1 hmem).2
  let ξ : realStandardModule (r + 1) ds := ⟨seedVector p m e, hps, fun p' d hd => by
    rw [hds, RealPrincipalSeriesDuality.realInducedBlockAt_map_character] at hd
    exact absurd hd (by simp)⟩
  refine ⟨ξ, hK', ?_⟩
  set N₁ := ⌈((r + 1 - 1 : ℕ) : ℝ) * q⌉₊ with hN₁
  refine ⟨max 1 (max ‖I‖⁻¹ (‖I‖⁻¹ * K)), 1, max r N₁, by positivity, one_pos,
    scaleUnits (r + 1), fun t => (scaleFactor s t * I)⁻¹, fun t ht => ⟨fun i => scaleUnits_pos t i,
      ?_, ?_, ?_⟩⟩
  · -- the height
    have ht0 : 0 < t := by linarith
    calc unitHeight (A := Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
          (Iwasawa.diagonalUnits (scaleUnits (r + 1) t)) ≤ t ^ (r + 1 - 1) :=
          unitHeight_scale_le ht
      _ = t ^ r := by rw [Nat.add_sub_cancel]
      _ ≤ t ^ (max r N₁) := pow_le_pow_right₀ ht (le_max_left _ _)
      _ = 1 * t ^ (max r N₁) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- the scalar
    have ht0 : 0 < t := by linarith
    rw [norm_inv, norm_mul, mul_inv]
    have h1 := norm_scaleFactor_inv_le (n := r + 1) s ht
    calc ‖scaleFactor s t‖⁻¹ * ‖I‖⁻¹ ≤ t ^ N₁ * ‖I‖⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ t ^ (max r N₁) * ‖I‖⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht (le_max_right _ _)) (by positivity)
      _ = ‖I‖⁻¹ * t ^ (max r N₁) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)
  · -- the pairing
    intro ψ L hψ hL hLip
    set μ := haarOrthogonal (r + 1) with hμ
    set A : Langlands.GeneralLinear (r + 1) ℝ := Iwasawa.diagonalUnits (scaleUnits (r + 1) t)
      with hA
    set c := scaleFactor s t with hcdef
    have hcpos : 0 < ‖c‖ := norm_scaleFactor_pos s t
    have hc : c ≠ 0 := norm_pos_iff.1 hcpos
    have hcov := isSignCovariant_of_isSignCompatible hψ
    have hpair : haarPairing (compactFunction ds ((c * I)⁻¹) A ξ) ψ =
        (c * I)⁻¹ * ∫ κ, seedProfile p m κ * extension s ψ (Unitary.toUnits κ * A⁻¹) ∂μ := by
      unfold haarPairing
      simp_rw [compactFunction_apply, mul_assoc]
      rw [integral_const_mul]
      congr 1
      have h := integral_translate_eq hχ hps A ψ
      change ∫ κ, seedVector p m e (Unitary.toUnits κ * A) * ψ κ ∂μ = _
      rw [h]
      simp only [seedVector_unitary]
      rfl
    rw [hpair]
    have hF : Integrable
        (fun κ => seedProfile p m κ * extension s ψ (Unitary.toUnits κ * A⁻¹)) μ :=
      OrthogonalFinitePolynomial.integrable_of_continuous μ ((continuous_seedProfile p m).mul
        (continuous_extension_translate s ψ A⁻¹))
    have hq2 : q ≤ 2 * m := by
      have : 0 ≤ (((r + 1 : ℕ) : ℝ) + 1) * q := by positivity
      nlinarith
    have hW := integrable_weight (n := r + 1) p hm1 s hq2
    have hG : Integrable (fun κ => c * weight p m s κ * ψ 1) μ :=
      (hW.const_mul c).mul_const (ψ 1)
    have hGint : ∫ κ, c * weight p m s κ * ψ 1 ∂μ = c * I * ψ 1 := by
      rw [integral_mul_const, integral_const_mul]
    have hdiff : (c * I)⁻¹ * (∫ κ, seedProfile p m κ * extension s ψ (Unitary.toUnits κ * A⁻¹) ∂μ)
        - ψ 1 = (c * I)⁻¹ * ∫ κ, (seedProfile p m κ * extension s ψ (Unitary.toUnits κ * A⁻¹) -
          c * weight p m s κ * ψ 1) ∂μ := by
      rw [integral_sub hF hG, hGint, mul_sub]
      congr 1
      field_simp
    rw [hdiff]
    have hbound : ‖∫ κ, (seedProfile p m κ * extension s ψ (Unitary.toUnits κ * A⁻¹) -
        c * weight p m s κ * ψ 1) ∂μ‖ ≤ ‖c‖ * (t⁻¹ * ((‖ψ‖ + L) * K)) := by
      have h := norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall fun κ => hK ψ L hL hcov hLip κ ht)
      have hμ1 : μ.real Set.univ = 1 := by simp [μ]
      rwa [hμ1, mul_one] at h
    have ht0 : 0 < t := by linarith
    rw [norm_mul, norm_inv, norm_mul, Real.rpow_neg_one]
    calc (‖c‖ * ‖I‖)⁻¹ * ‖∫ κ, (seedProfile p m κ * extension s ψ (Unitary.toUnits κ * A⁻¹) -
          c * weight p m s κ * ψ 1) ∂μ‖ ≤ (‖c‖ * ‖I‖)⁻¹ * (‖c‖ * (t⁻¹ * ((‖ψ‖ + L) * K))) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ‖I‖⁻¹ * K * t⁻¹ * (‖ψ‖ + L) := by
          field_simp
      _ ≤ max 1 (max ‖I‖⁻¹ (‖I‖⁻¹ * K)) * t⁻¹ * (‖ψ‖ + L) := by
          gcongr
          exact (le_max_right _ _).trans (le_max_right _ _)


end Langlands.Global.RankinSelbergGlobal.RealStandardCompactDirac
