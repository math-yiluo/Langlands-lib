import Langlands.Global.RankinSelberg.UnequalAnalyticProof
import Langlands.Global.RankinSelberg.UnfoldingDualGL
import Langlands.Automorphic.OperatorDeterminantSliceGeometry
import Langlands.Automorphic.IrreducibleCentralCharacterProof

/-! # Cusp forms grow at most like a fixed power of `|det|`

For an actual cuspidal operator realization of `GL_n` there is one real exponent `β`,
depending only on the realization, such that every realized cusp form `φ` satisfies
`|φ(g)| ≤ C_φ |det g|^β` on all of `GL_n(𝔸)`. The exponent comes from the central character;
the constant from boundedness on the norm-one elements (Siegel decomposition and decay on the
chamber). The same holds for the dual functions `g ↦ φ(w ᵗg⁻¹)`, with exponent `-β`. -/

noncomputable section
universe u
set_option autoImplicit false

open scoped NNReal
open NumberField Langlands.Global Langlands.Automorphic
  Langlands.Automorphic.CuspidalL2 Langlands.Automorphic.ContinuousRationalFunctions

namespace Langlands.Global.RankinSelbergGlobal.CuspCentralBound

variable {F : Type u} [Field F] [NumberField F]

/-! ### Boundedness on the norm-one elements -/

/-- A cuspidal realized vector is bounded on the adelic matrices of determinant norm one. -/
theorem exists_norm_evaluate_le_of_absDet_eq_one [CompactSpace (AdeleQuotient F)] {n : ℕ}
    (S : OperatorRealization F n) (hS : S.IsCuspidal) (f : S.Space) :
    ∃ C : ℝ, ∀ g : AdelicGL F n, absDet F n g = 1 →
      ‖evaluate F n (S.toContinuous f) g‖ ≤ C := by
  obtain ⟨Q₁, K, hQ₁, hK, hdec⟩ := exists_siegelDecomposition F n
  obtain ⟨L, hL⟩ := UnequalAnalytic.exists_abs_log_absDet_le (F := F) (n := n) hQ₁
  have hd : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  obtain ⟨C, hC⟩ := S.exists_chamber_decay hS f Q₁ hQ₁ (R := L / Module.finrank ℚ F) hK
    (le_refl (0 : ℝ))
  refine ⟨C, fun g hg => ?_⟩
  obtain ⟨γ, x, q, hq, hγ, hx⟩ := hdec g
  have hlog := UnequalAnalytic.log_absDet_torInf_mul (F := F) x q
  rw [← hγ, absDet_rational_mul, hg, Real.log_one] at hlog
  have hsum : |∑ i, x i| ≤ L / Module.finrank ℚ F := by
    rw [le_div_iff₀ hd]
    have h1 : Real.log (absDet F n q) = -((Module.finrank ℚ F : ℝ) * ∑ i, x i) := by linarith
    have h2 : |∑ i, x i| * (Module.finrank ℚ F : ℝ) = |Real.log (absDet F n q)| := by
      rw [h1, abs_neg, abs_mul, abs_of_pos hd, mul_comm]
    rw [h2]
    exact hL q hq
  have hb := hC x hx hsum q hq
  rw [zero_mul, neg_zero, Real.exp_zero, mul_one] at hb
  rw [← evaluate_rational F n (S.toContinuous f) γ g, hγ]
  exact hb

/-! ### Continuous characters of the positive reals -/

theorem expUnit_zero : expUnit 0 = 1 := by
  apply Units.ext; apply NNReal.eq; simp

theorem expUnit_neg (y : ℝ) : expUnit (-y) = (expUnit y)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← expUnit_add, neg_add_cancel, expUnit_zero]

theorem continuous_expUnit : Continuous expUnit := by
  have hv : Continuous fun y : ℝ => ((expUnit y : ℝ≥0ˣ) : ℝ≥0) :=
    Real.continuous_exp.subtype_mk _
  refine Units.continuous_iff.mpr ⟨hv, ?_⟩
  have h : (fun y : ℝ => (((expUnit y)⁻¹ : ℝ≥0ˣ) : ℝ≥0)) =
      fun y => ((expUnit (-y) : ℝ≥0ˣ) : ℝ≥0) := by
    funext y; rw [expUnit_neg]
  rw [h]
  exact hv.comp continuous_neg

/-- The norm of a continuous character of the positive real units is a real power. -/
theorem exists_norm_character_expUnit (ω : ℝ≥0ˣ →ₜ* ℂˣ) :
    ∃ α : ℝ, ∀ y : ℝ, ‖((ω (expUnit y) : ℂˣ) : ℂ)‖ = Real.exp (α * y) := by
  have hpos : ∀ y : ℝ, 0 < ‖((ω (expUnit y) : ℂˣ) : ℂ)‖ := fun y =>
    norm_pos_iff.mpr (Units.ne_zero _)
  let A : ℝ →+ ℝ :=
    { toFun := fun y => Real.log ‖((ω (expUnit y) : ℂˣ) : ℂ)‖
      map_zero' := by simp [expUnit_zero]
      map_add' := fun x y => by
        simp only [expUnit_add, map_mul, Units.val_mul, norm_mul]
        exact Real.log_mul (hpos x).ne' (hpos y).ne' }
  have hA : Continuous A := by
    have h1 : Continuous fun y : ℝ => ‖((ω (expUnit y) : ℂˣ) : ℂ)‖ :=
      (Units.continuous_val.comp (ω.continuous.comp continuous_expUnit)).norm
    exact h1.log fun y => (hpos y).ne'
  refine ⟨A 1, fun y => ?_⟩
  have h := map_real_smul A hA y 1
  simp only [smul_eq_mul, mul_one] at h
  have hAy : A y = Real.log ‖((ω (expUnit y) : ℂˣ) : ℂ)‖ := rfl
  rw [← Real.exp_log (hpos y), ← hAy, h, mul_comm]

/-! ### The power bound on the adelic matrix group -/

/-- The determinant norm of a positive real scalar idele. -/
theorem absDet_scalar_full_expUnit (n : ℕ) (y : ℝ) :
    absDet F n (AdelicGL.scalar F n (PositiveRealIdeles.full F (expUnit y))) =
      Real.exp (((Module.finrank ℚ F * n : ℕ) : ℝ) * y) := by
  have h1 : absDet F n (AdelicGL.scalar F n (PositiveRealIdeles.full F (expUnit y))) =
      (((AdelicBlockDeterminantCharacter.determinantNorm F n
        (AdelicGL.scalar F n (PositiveRealIdeles.full F (expUnit y))) : ℝ≥0ˣ) : ℝ≥0) : ℝ) :=
    rfl
  rw [h1, AdelicBlockDeterminantCharacter.determinantNorm_scalar,
    PositiveRealIdeles.absoluteValue_full, ← pow_mul, Units.val_pow_eq_pow_val, NNReal.coe_pow,
    coe_expUnit, ← Real.exp_nat_mul]

/-- **Central power bound.** For a cuspidal realization with a central character there is one
exponent `β` such that each realized vector is bounded by `C |det g|^β` on `GL_n(𝔸)`. -/
theorem exists_norm_evaluate_le_rpow [CompactSpace (AdeleQuotient F)] {n : ℕ} (hn : n ≠ 0)
    (S : OperatorRealization F n) (hS : S.IsCuspidal) (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : S.HasCentralCharacter χ) :
    ∃ β : ℝ, ∀ f : S.Space, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : AdelicGL F n,
      ‖evaluate F n (S.toContinuous f) g‖ ≤ C * absDet F n g ^ β := by
  obtain ⟨α, hα⟩ := exists_norm_character_expUnit
    ((centralIdeleCharacter F χ).comp (PositiveRealIdeles.full F))
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = ((Module.finrank ℚ F * n : ℕ) : ℝ) := ⟨_, rfl⟩
  have hk : 0 < k := by
    rw [hkdef]
    exact Nat.cast_pos.mpr (Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hn))
  refine ⟨α / k, fun f => ?_⟩
  obtain ⟨C, hC⟩ := exists_norm_evaluate_le_of_absDet_eq_one S hS f
  refine ⟨max C 0, le_max_right _ _, fun g => ?_⟩
  have hg := absDet_pos F n g
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = -Real.log (absDet F n g) / k := ⟨_, rfl⟩
  have hαy := hα y
  simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply] at hαy
  have hz : absDet F n
      (AdelicGL.scalar F n (PositiveRealIdeles.full F (expUnit y)) * g) = 1 := by
    rw [absDet_mul, absDet_scalar_full_expUnit, ← hkdef, hydef,
      mul_div_cancel₀ _ hk.ne', Real.exp_neg, Real.exp_log hg, inv_mul_cancel₀ hg.ne']
  have hb := hC _ hz
  rw [S.centralCharacter_evaluate χ hχ f _ g, norm_mul, hαy] at hb
  have hpow : Real.exp (-(α * y)) = absDet F n g ^ (α / k) := by
    rw [Real.rpow_def_of_pos hg, hydef]
    congr 1
    field_simp
  have hnn : 0 ≤ absDet F n g ^ (α / k) := Real.rpow_nonneg hg.le _
  have hone : Real.exp (-(α * y)) * Real.exp (α * y) = 1 := by
    rw [← Real.exp_add, neg_add_cancel (α * y), Real.exp_zero]
  calc ‖evaluate F n (S.toContinuous f) g‖
      = Real.exp (-(α * y)) *
          (Real.exp (α * y) * ‖evaluate F n (S.toContinuous f) g‖) := by
        rw [← mul_assoc, hone, one_mul]
    _ ≤ Real.exp (-(α * y)) * C := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ max C 0 * absDet F n g ^ (α / k) := by
        rw [hpow, mul_comm]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnn

/-! ### The power bound for cusp functions on group-scheme points -/

variable (F)

theorem detNorm_eq_absDet (n : ℕ) (g : Points F n) :
    detNorm F n g = absDet F n (GeneralLinearGroupPoints.adelicHomeomorph F n g) := rfl

/-- **Cusp forms are bounded by a fixed power of `|det|`.** The exponent depends only on the
realization; the constant depends on the vector. -/
theorem exists_norm_cuspFunction_le [CompactSpace (AdeleQuotient F)] {t : ℕ}
    (T' : CuspidalOperatorRealization F t) :
    ∃ β : ℝ, ∀ v' : T'.Space, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Points F (t + 1),
      ‖cuspFunction F T' v' g‖ ≤ C * detNorm F (t + 1) g ^ β := by
  obtain ⟨χ, hχ, -⟩ := OperatorRealization.irreducibleCentralCharacter F (t + 1)
    T'.realization T'.irreducible
  obtain ⟨β, hβ⟩ := exists_norm_evaluate_le_rpow (Nat.succ_ne_zero t) T'.realization
    T'.cuspidal χ hχ
  refine ⟨β, fun v' => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hβ v'
  refine ⟨C, hC0, fun g => ?_⟩
  rw [UnequalAnalytic.cuspFunction_eq F T' v', detNorm_eq_absDet]
  exact hC _

/-- The determinant norm of the dual point `w ᵗg⁻¹` is the inverse determinant norm. -/
theorem detNorm_dualPoint (n : ℕ) (g : Points F n) :
    detNorm F n (Unfolding.dualPoint F n g) = (detNorm F n g)⁻¹ := by
  have hw : AdelicBlockDeterminantCharacter.determinantNorm F n
      (GeneralLinear.weylLong n (Adeles F)) = 1 := by
    obtain ⟨a, ha⟩ : ∃ a, a = AdelicBlockDeterminantCharacter.determinantNorm F n
        (GeneralLinear.weylLong n (Adeles F)) := ⟨_, rfl⟩
    have h1 : a * a = 1 := by
      rw [ha, ← map_mul, GeneralLinear.weylLong_mul_self, map_one]
    have h2 : ((a : ℝ≥0) : ℝ) * ((a : ℝ≥0) : ℝ) = 1 := by
      have := congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) h1
      simpa using this
    have h3 : 0 ≤ ((a : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have h4 : ((a : ℝ≥0) : ℝ) = 1 := by nlinarith
    rw [← ha]
    apply Units.ext
    apply NNReal.eq
    simpa using h4
  have hdet : ∀ G : AdelicGL F n,
      AdelicGL.determinant F n (GeneralLinear.inverseTranspose n (Adeles F) G) =
        AdelicGL.determinant F n G⁻¹ := by
    intro G
    apply Units.ext
    show Matrix.det ((G⁻¹ : AdelicGL F n).val.transpose) = Matrix.det (G⁻¹ : AdelicGL F n).val
    exact Matrix.det_transpose _
  have hinv : ∀ G : AdelicGL F n, AdelicBlockDeterminantCharacter.determinantNorm F n
      (GeneralLinear.inverseTranspose n (Adeles F) G) =
        (AdelicBlockDeterminantCharacter.determinantNorm F n G)⁻¹ := by
    intro G
    show IdeleAbsoluteValue.full F (AdelicGL.determinant F n _) = _
    rw [hdet, map_inv, map_inv]
    rfl
  simp only [detNorm, Unfolding.dualPoint, MulEquiv.apply_symm_apply, map_mul, hw, one_mul,
    hinv]
  rw [Units.val_inv_eq_inv_val, NNReal.coe_inv]

/-- **Dual cusp forms are bounded by a fixed power of `|det|`.** -/
theorem exists_norm_dualCuspFunction_le [CompactSpace (AdeleQuotient F)] {t : ℕ}
    (T' : CuspidalOperatorRealization F t) :
    ∃ β : ℝ, ∀ v' : T'.Space, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Points F (t + 1),
      ‖dualFunction F (t + 1) (cuspFunction F T' v') g‖ ≤ C * detNorm F (t + 1) g ^ β := by
  obtain ⟨β, hβ⟩ := exists_norm_cuspFunction_le F T'
  refine ⟨-β, fun v' => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hβ v'
  refine ⟨C, hC0, fun g => ?_⟩
  rw [Unfolding.dualFunction_eq]
  refine (hC _).trans (le_of_eq ?_)
  rw [detNorm_dualPoint, Real.inv_rpow (Unfolding.detNorm_pos F (t + 1) g).le, Real.rpow_neg
    (Unfolding.detNorm_pos F (t + 1) g).le]

end Langlands.Global.RankinSelbergGlobal.CuspCentralBound
