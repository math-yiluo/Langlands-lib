import Langlands.Global.RankinSelberg.AdelicSchwartzMellinHaar
import Langlands.Global.RankinSelberg.EqualAnalyticEisensteinInvariance
import Langlands.Global.RankinSelberg.EqualAnalyticThetaBound

/-! # Bounds for the theta series on the scalar idele fibres -/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands.Global
open scoped CategoryTheory.MonObj Matrix ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open EqualAnalytic

namespace Eisenstein

local instance schemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance schemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

/-- Every idele has a principal translate given by its norm and a point of one compact set. -/
private theorem exists_compact_ideleRepresentatives :
    ∃ C : Set (Points F 1), IsCompact C ∧ ∀ a : Points F 1,
      ∃ f : Fˣ, ∃ b ∈ C, ratUnit F f * a = normScale F (logNorm F a) * b := by
  let iso := AdelicSchwartzMellin.ideleContinuousEquiv F
  obtain ⟨C, hC, _, hrep⟩ := NormOneIdeleClass.exists_isCompact_fundamentalSet F
  refine ⟨iso.symm '' C, hC.image iso.symm.continuous, fun a => ?_⟩
  let y := logNorm F a
  let a₁ := normScale F (-y) * a
  have ha₁ : detNorm F 1 a₁ = 1 := by
    rw [detNorm_one_mul, detNorm_normScale, Real.exp_neg, show y = logNorm F a from rfl,
      logNorm, Real.exp_log (UnequalAnalytic.detNorm_pos F a),
      inv_mul_cancel₀ (UnequalAnalytic.detNorm_pos F a).ne']
  have ha₁' : iso a₁ ∈ NormOneIdeleClass.normOneIdeles F := by
    apply Units.ext
    apply NNReal.eq
    exact ha₁
  obtain ⟨f, hf⟩ := hrep (iso a₁) ha₁'
  have hb : iso (ratUnit F f * a₁) = diagonalUnits F f * iso a₁ := by
    rw [map_mul]
    congr 1
    exact ideleOf_ratUnit F f
  refine ⟨f, ratUnit F f * a₁, ⟨_, hb ▸ hf, iso.symm_apply_apply _⟩, ?_⟩
  rw [show a₁ = normScale F (-y) * a from rfl, ← mul_assoc,
    points_one_mul_comm F (normScale F y) (ratUnit F f), mul_assoc,
    ← mul_assoc (normScale F y), ← normScale_add, add_neg_cancel, normScale_zero, one_mul]

/-- A continuous idele class character has at most exponential growth in the log norm. -/
theorem exists_ideleChar_bound (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    ∃ β C : ℝ, 0 ≤ C ∧ ∀ a, ‖ideleChar F χ a‖ ≤ C * Real.exp (β * logNorm F a) := by
  obtain ⟨C, hC, hcover⟩ := exists_compact_ideleRepresentatives F
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (continuous_ideleChar F χ).continuousOn
  obtain ⟨w, hw⟩ := exists_eq_cexp_of_continuous (f := fun y => ideleChar F χ (normScale F y))
    ((continuous_ideleChar F χ).comp (continuous_normScale F))
    (by simp only [normScale_zero, ideleChar_one]) (fun y z => by simp [normScale_add, ideleChar_mul])
  refine ⟨w.re, max B 0, le_max_right _ _, fun a => ?_⟩
  obtain ⟨f, b, hb, hab⟩ := hcover a
  have hχa := ideleChar_ideleRational_mul F χ ⟨ratUnit F f, ratUnit_mem F f⟩ a
  change ideleChar F χ (ratUnit F f * a) = ideleChar F χ a at hχa
  rw [← hχa, hab, ideleChar_mul, hw, norm_mul, Complex.norm_exp, Complex.re_mul_ofReal,
    mul_comm]
  exact mul_le_mul_of_nonneg_right ((hB b hb).trans (le_max_left _ _)) (Real.exp_pos _).le

private theorem adelicEquiv_zeta_normScale (n : ℕ) (y : ℝ) :
    e n (zeta F n (normScale F y)) =
      AdelicGL.ofInfinite F n (torInf F n fun _ => y / Module.finrank ℚ F) := by
  rw [show e n (zeta F n (normScale F y)) = AdelicGL.scalar F n (ideleOf F (normScale F y))
    from adelicEquiv_zeta F n _, normScale]
  apply Units.ext
  change Matrix.scalar (Fin n) (↑(ideleOf F ((e 1).symm _)) : Adeles F) = _
  rw [Matrix.scalar_apply, ofInfinite_torInf_val]
  congr 1
  funext i
  change Matrix.det ((e 1 ((e 1).symm _)) : Matrix (Fin 1) (Fin 1) (Adeles F)) = _
  rw [ContinuousMulEquiv.apply_symm_apply, ofInfinite_torInf_val, Matrix.det_fin_one,
    Matrix.diagonal_apply_eq]

/-- The scalar of a principal idele is a rational element of the adelic general linear group. -/
theorem adelicEquiv_zeta_ratUnit (n : ℕ) (f : Fˣ) :
    e n (zeta F n (ratUnit F f)) = AdelicGL.rational F n (Matrix.GeneralLinearGroup.scalar (Fin n) f) := by
  rw [show e n (zeta F n (ratUnit F f)) = AdelicGL.scalar F n (ideleOf F (ratUnit F f))
    from adelicEquiv_zeta F n _, ideleOf_ratUnit]
  apply Units.ext
  change Matrix.scalar (Fin n) (algebraMap F (Adeles F) (f : F)) =
    (Matrix.scalar (Fin n) (f : F)).map (algebraMap F (Adeles F))
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]

/-- The theta series evaluated at the scalar translate `a g`. -/
abbrev scalarTheta (n : ℕ) (Φ : RowVector F n → ℂ) (g : Points F n) (a : Points F 1) : ℂ :=
  thetaSum F n Φ (e n (zeta F n a * g))

/-- The sum of the absolute values of the nonzero terms of `scalarTheta`. -/
abbrev scalarThetaNorm (n : ℕ) (Φ : RowVector F n → ℂ) (g : Points F n) (a : Points F 1) : ℝ≥0∞ :=
  thetaNorm F n Φ (e n (zeta F n a * g))

theorem scalarTheta_ratUnit_mul (n : ℕ) (Φ : RowVector F n → ℂ) (g : Points F n) (f : Fˣ)
    (a : Points F 1) : scalarTheta F n Φ g (ratUnit F f * a) = scalarTheta F n Φ g a := by
  simp only [scalarTheta, zeta_mul, mul_assoc, map_mul, adelicEquiv_zeta_ratUnit, thetaSum_rational_mul]

private theorem scalarThetaNorm_ratUnit_mul (n : ℕ) (Φ : RowVector F n → ℂ) (g : Points F n) (f : Fˣ)
    (a : Points F 1) : scalarThetaNorm F n Φ g (ratUnit F f * a) = scalarThetaNorm F n Φ g a := by
  simp only [scalarThetaNorm, zeta_mul, mul_assoc, map_mul, adelicEquiv_zeta_ratUnit, thetaNorm_rational_mul]

/-- Uniform exponential bounds for the scalar theta majorant with `g` in a compact set. -/
theorem exists_scalarThetaNorm_bound (n : ℕ) {Φ : RowVector F n → ℂ} (hΦ : IsRowDominated F n Φ)
    {K : Set (Points F n)} (hK : IsCompact K) (N : ℕ) (hN : n * Module.finrank ℚ F < N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ K, ∀ a, scalarThetaNorm F n Φ g a ≤
      ENNReal.ofReal (B * Real.exp (-(N / (Module.finrank ℚ F : ℝ)) * logNorm F a)) := by
  obtain ⟨C, hC, hcover⟩ := exists_compact_ideleRepresentatives F
  let q : Points F 1 × Points F n → AdelicGL F n := fun p => e n (zeta F n p.1 * p.2)
  have hQ : IsCompact (q '' (C ×ˢ K)) := (hC.prod hK).image
    ((e n).continuous.comp (((continuous_zeta F n).comp continuous_fst).mul continuous_snd))
  obtain ⟨B, hB, hbound⟩ := exists_thetaNorm_le F n hΦ hQ N hN
  refine ⟨B, hB, fun g hg a => ?_⟩
  obtain ⟨f, b, hb, hab⟩ := hcover a
  rw [← scalarThetaNorm_ratUnit_mul F n Φ g f a, hab]
  simp only [scalarThetaNorm, zeta_mul, mul_assoc, map_mul, adelicEquiv_zeta_normScale]
  have hq : q (b, g) ∈ q '' (C ×ˢ K) := ⟨(b, g), ⟨hb, hg⟩, rfl⟩
  have h := hbound (fun _ => logNorm F a / Module.finrank ℚ F) (logNorm F a / Module.finrank ℚ F)
    (fun _ => le_rfl) _ hq
  rw [show -(N * (logNorm F a / Module.finrank ℚ F)) =
    -(N / (Module.finrank ℚ F : ℝ)) * logNorm F a by ring] at h
  simpa only [q, map_mul] using h

end Eisenstein
end Langlands.Global.RankinSelbergGlobal
