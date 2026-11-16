import Langlands.Global.RankinSelberg.EqualAnalyticEisenstein

/-! # Invariance of the Eisenstein series

The section and Eisenstein series of `EqualIntegrals` satisfy, without any convergence
assumption (the integrals and sums being the unconditional ones of the definition):

* `F(p g) = F(g)` for `p ∈ P'(F)` (`eisensteinSection_parabolic_mul`), hence
  `E(γ g) = E(g)` for `γ ∈ GL_n(F)` (`eisensteinSeries_rational_mul`), by reindexing the cosets;
* `F(a g) = χ(a)⁻¹ F(g)` and `E(a g) = χ(a)⁻¹ E(g)` for a scalar idele `a`
  (`eisensteinSection_zeta_mul`, `eisensteinSeries_zeta_mul`), by the substitution
  `a' ↦ a⁻¹ a'` in `d^×a'`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance invSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance invSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F

theorem eisensteinSectionIntegrand_eq' (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (x : Points F (r + 1)) (z : Points F 1) :
    eisensteinSectionIntegrand F χ Φ s x z =
      Φ ((ideleOf F z : Adeles F) • lastRow F r x) * sectionWeight (F := F) r χ s z := by
  simp only [eisensteinSectionIntegrand, sectionWeight, ideleChar, mul_assoc]

theorem rationalPoint_mul (c c' : RationalGL F (r + 1)) :
    rationalPoint F (r + 1) (c * c') = rationalPoint F (r + 1) c * rationalPoint F (r + 1) c' := by
  simp only [rationalPoint, map_mul]

theorem lastRow_parabolic_mul (p : RationalGL F (r + 1)) {a : F}
    (ha : rowOf F r p = a • rowOf F r 1) (x : Points F (r + 1)) :
    lastRow F r (rationalPoint F (r + 1) p * x) = algebraMap F (Adeles F) a • lastRow F r x := by
  rw [lastRow_rationalPoint_mul, ha, ratRow_smul, Matrix.smul_mul, ← lastRow_eq]

/-- The section is invariant under `P'(F)`. -/
theorem eisensteinSection_parabolic_mul (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (p : RationalGL F (r + 1))
    (hp : p ∈ eisensteinParabolic F r) (x : Points F (r + 1)) :
    eisensteinSection F χ Φ s (rationalPoint F (r + 1) p * x) = eisensteinSection F χ Φ s x := by
  obtain ⟨a, ha⟩ := (mem_eisensteinParabolic_iff F r p).1 hp
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact rowOf_ne_zero F r p ha
  set u : Fˣ := Units.mk0 a ha0
  unfold eisensteinSection
  rw [detPower_rationalPoint_mul]
  congr 1
  have h1 : ∀ z, eisensteinSectionIntegrand F χ Φ s (rationalPoint F (r + 1) p * x) z =
      eisensteinSectionIntegrand F χ Φ s x (ratUnit F u * z) := by
    intro z
    have hcoe : ((diagonalUnits F u * ideleOf F z : Ideles F) : Adeles F) =
        (ideleOf F z : Adeles F) * algebraMap F (Adeles F) a := by
      rw [Units.val_mul, mul_comm]
      rfl
    rw [eisensteinSectionIntegrand_eq', eisensteinSectionIntegrand_eq',
      sectionWeight_ratUnit_mul, lastRow_parabolic_mul F r p ha, smul_smul, ideleOf_mul,
      ideleOf_ratUnit, hcoe]
  simp only [h1]
  exact integral_mul_left_eq_self (fun z => eisensteinSectionIntegrand F χ Φ s x z) _

/-- Right translation of the cosets `P'(F) \ GL_n(F)`. -/
def cosetRightEquiv (c : RationalGL F (r + 1)) :
    LeftCosetSpace (eisensteinParabolic F r) ≃ LeftCosetSpace (eisensteinParabolic F r) where
  toFun := LeftCosetSpace.rightTranslate _ c
  invFun := LeftCosetSpace.rightTranslate _ c⁻¹
  left_inv q := by
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ q
    simp only [LeftCosetSpace.rightTranslate_mk, mul_inv_cancel_right]
  right_inv q := by
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ q
    simp only [LeftCosetSpace.rightTranslate_mk, inv_mul_cancel_right]

/-- **The Eisenstein series is invariant under `GL_n(F)`.** -/
theorem eisensteinSeries_rational_mul (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (c : RationalGL F (r + 1)) (g : Points F (r + 1)) :
    eisensteinSeries F χ Φ s (rationalPoint F (r + 1) c * g) = eisensteinSeries F χ Φ s g := by
  unfold eisensteinSeries
  conv_rhs => rw [← (cosetRightEquiv F r c).tsum_eq]
  refine tsum_congr fun q => ?_
  obtain ⟨y, hydef⟩ : ∃ y, y = Quotient.out ((cosetRightEquiv F r c) q) := ⟨_, rfl⟩
  obtain ⟨x, hxdef⟩ : ∃ x, x = Quotient.out q * c := ⟨_, rfl⟩
  have h1 : LeftCosetSpace.mk (eisensteinParabolic F r) y = cosetRightEquiv F r c q := by
    rw [hydef]
    exact mk_out F r _
  have h2 : cosetRightEquiv F r c q = LeftCosetSpace.mk (eisensteinParabolic F r) x := by
    rw [hxdef]
    show LeftCosetSpace.rightTranslate _ c q = _
    conv_lhs => rw [← mk_out F r q]
    exact LeftCosetSpace.rightTranslate_mk _ c _
  have hp : y * x⁻¹ ∈ eisensteinParabolic F r :=
    (LeftCosetSpace.mk_eq_mk_iff _ x y).1 (h2.symm.trans h1.symm)
  have hy : y = (y * x⁻¹) * x := by rw [inv_mul_cancel_right]
  rw [← mul_assoc, ← rationalPoint_mul, ← hxdef, ← hydef]
  conv_rhs => rw [hy, rationalPoint_mul, mul_assoc, eisensteinSection_parabolic_mul F r χ Φ s _ hp]

theorem detPower_one_mul (a b : Points F 1) (w : ℂ) :
    detPower F 1 (a * b) w = detPower F 1 a w * detPower F 1 b w := by
  rw [detPower, detPower, detPower, detNorm_one_mul, Real.log_mul
    (UnequalAnalytic.detNorm_pos F a).ne' (UnequalAnalytic.detNorm_pos F b).ne',
    Complex.ofReal_add, mul_add, Complex.exp_add]

theorem sectionWeight_mul (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (s : ℂ) (a b : Points F 1) :
    sectionWeight (F := F) r χ s (a * b) =
      sectionWeight (F := F) r χ s a * sectionWeight (F := F) r χ s b := by
  simp only [sectionWeight, detPower_one_mul, ideleChar_mul]
  ring

theorem sectionWeight_one (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (s : ℂ) :
    sectionWeight (F := F) r χ s 1 = 1 := by
  simp only [sectionWeight, detPower, ideleChar_one]
  have : detNorm F 1 (1 : Points F 1) = 1 := by
    have h := detNorm_one_mul F 1 1
    rw [one_mul] at h
    have hp := UnequalAnalytic.detNorm_pos F (1 : Points F 1)
    field_simp at h
    linarith
  rw [this, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]

theorem detPower_zeta_mul (a : Points F 1) (x : Points F (r + 1)) (s : ℂ) :
    detPower F (r + 1) (zeta F (r + 1) a * x) s =
      detPower F 1 a ((r + 1 : ℂ) * s) * detPower F (r + 1) x s := by
  rw [detPower, detPower, detPower, log_detNorm_zeta_mul, ← Complex.exp_add]
  congr 1
  push_cast
  rw [logNorm]
  ring

theorem lastRow_zeta_mul (a : Points F 1) (x : Points F (r + 1)) :
    lastRow F r (zeta F (r + 1) a * x) = (ideleOf F a : Adeles F) • lastRow F r x := by
  rw [lastRow_eq, lastRow_eq, map_mul, adelicEquiv_zeta, Units.val_mul,
    show ((AdelicGL.scalar F (r + 1) (ideleOf F a) : AdelicGL F (r + 1)) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) =
      Matrix.scalar (Fin (r + 1)) ((ideleOf F a : Ideles F) : Adeles F) from rfl,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.mul_smul]

/-- The section transforms by `χ⁻¹` under scalars. -/
theorem eisensteinSection_zeta_mul (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (a : Points F 1) (x : Points F (r + 1)) :
    eisensteinSection F χ Φ s (zeta F (r + 1) a * x) =
      (ideleChar F χ a)⁻¹ * eisensteinSection F χ Φ s x := by
  unfold eisensteinSection
  have h1 : ∀ z, eisensteinSectionIntegrand F χ Φ s (zeta F (r + 1) a * x) z =
      (fun z' => Φ ((ideleOf F z' : Adeles F) • lastRow F r x) *
        sectionWeight (F := F) r χ s (a⁻¹ * z')) (a * z) := by
    intro z
    simp only
    have hcoe : ((ideleOf F a * ideleOf F z : Ideles F) : Adeles F) =
        (ideleOf F z : Adeles F) * (ideleOf F a : Adeles F) := by
      rw [Units.val_mul, mul_comm]
    rw [eisensteinSectionIntegrand_eq', lastRow_zeta_mul, smul_smul, inv_mul_cancel_left,
      ideleOf_mul, hcoe]
  simp only [h1]
  rw [integral_mul_left_eq_self (fun z' => Φ ((ideleOf F z' : Adeles F) • lastRow F r x) *
    sectionWeight (F := F) r χ s (a⁻¹ * z')) a]
  have h2 : ∀ z', Φ ((ideleOf F z' : Adeles F) • lastRow F r x) *
      sectionWeight (F := F) r χ s (a⁻¹ * z') =
      sectionWeight (F := F) r χ s a⁻¹ * eisensteinSectionIntegrand F χ Φ s x z' := by
    intro z'
    rw [sectionWeight_mul, eisensteinSectionIntegrand_eq']
    ring
  simp only [h2]
  rw [integral_const_mul, detPower_zeta_mul]
  have h3 : sectionWeight (F := F) r χ s a⁻¹ * sectionWeight (F := F) r χ s a = 1 := by
    rw [← sectionWeight_mul, inv_mul_cancel, sectionWeight_one]
  have h4 : sectionWeight (F := F) r χ s a =
      detPower F 1 a ((r + 1 : ℂ) * s) * ideleChar F χ a := rfl
  have hχ := ideleChar_ne_zero F χ a
  have h5 : sectionWeight (F := F) r χ s a⁻¹ =
      (detPower F 1 a ((r + 1 : ℂ) * s))⁻¹ * (ideleChar F χ a)⁻¹ := by
    rw [eq_comm, ← mul_inv, ← h4]
    exact (eq_inv_of_mul_eq_one_left h3).symm
  rw [h5]
  have hd : detPower F 1 a ((r + 1 : ℂ) * s) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- **The Eisenstein series transforms by `χ⁻¹` under scalars.** -/
theorem eisensteinSeries_zeta_mul (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (a : Points F 1) (g : Points F (r + 1)) :
    eisensteinSeries F χ Φ s (zeta F (r + 1) a * g) =
      (ideleChar F χ a)⁻¹ * eisensteinSeries F χ Φ s g := by
  unfold eisensteinSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [← mul_assoc, ← zeta_mul_comm, mul_assoc, eisensteinSection_zeta_mul]

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
