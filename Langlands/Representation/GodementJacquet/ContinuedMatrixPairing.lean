import Langlands.Representation.GodementJacquet.ZetaLinear

/-! # Bilinear rational values of actual matrix integrals -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory RankinSelberg
open RankinSelberg.RationalContinuationLinear

universe uF uW

section TestLinearity

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  {abv : AbsoluteValue F ℝ} {Φ Ψ : MatrixTestFunction n F} {s : ℂ}
  {f : Langlands.GeneralLinear (n + 1) F → ℂ}

@[simp] theorem matrixIntegrand_zero_test :
    matrixIntegrand abv (0 : MatrixTestFunction n F) s f = 0 := by
  funext g
  simp [matrixIntegrand]

theorem matrixIntegrand_add_test :
    matrixIntegrand abv (Φ + Ψ) s f =
      matrixIntegrand abv Φ s f + matrixIntegrand abv Ψ s f := by
  funext g
  change (Φ g.val + Ψ g.val) * f g * _ =
    Φ g.val * f g * _ + Ψ g.val * f g * _
  ring

theorem matrixIntegrand_smul_test (c : ℂ) :
    matrixIntegrand abv (c • Φ) s f = c • matrixIntegrand abv Φ s f := by
  funext g
  change (c * Φ g.val) * f g * _ = c * (Φ g.val * f g * _)
  ring

variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  {μ : Measure (Langlands.GeneralLinear (n + 1) F)}

theorem matrixConverges_zero_test :
    MatrixConverges abv μ (0 : MatrixTestFunction n F) s f := by
  simp [MatrixConverges]

theorem MatrixConverges.add_test
    (hΦ : MatrixConverges abv μ Φ s f)
    (hΨ : MatrixConverges abv μ Ψ s f) :
    MatrixConverges abv μ (Φ + Ψ) s f := by
  rw [MatrixConverges, matrixIntegrand_add_test]
  exact Integrable.add hΦ hΨ

theorem MatrixConverges.smul_test
    (hΦ : MatrixConverges abv μ Φ s f) (c : ℂ) :
    MatrixConverges abv μ (c • Φ) s f := by
  rw [MatrixConverges, matrixIntegrand_smul_test]
  exact Integrable.smul c hΦ

theorem matrixIntegral_add_test
    (hΦ : MatrixConverges abv μ Φ s f)
    (hΨ : MatrixConverges abv μ Ψ s f) :
    matrixIntegral abv μ (Φ + Ψ) s f =
      matrixIntegral abv μ Φ s f + matrixIntegral abv μ Ψ s f := by
  unfold matrixIntegral
  rw [matrixIntegrand_add_test]
  exact integral_add hΦ hΨ

theorem matrixIntegral_smul_test (c : ℂ) :
    matrixIntegral abv μ (c • Φ) s f =
      c * matrixIntegral abv μ Φ s f := by
  unfold matrixIntegral
  rw [matrixIntegrand_smul_test]
  exact integral_const_mul c _

theorem hasShiftedRationalValue_zero_test (q : ℕ) :
    HasShiftedRationalValue q abv μ (0 : MatrixTestFunction n F) f 0 := by
  constructor
  · exact ⟨0, fun _ _ => matrixConverges_zero_test⟩
  · refine ⟨0, fun s _ => ?_⟩
    simp [matrixIntegral]

/-- Addition in the test variable preserves actual shifted rational values. -/
theorem HasShiftedRationalValue.add_test {q : ℕ} {R S : RationalFunctions}
    (hR : HasShiftedRationalValue q abv μ Φ f R)
    (hS : HasShiftedRationalValue q abv μ Ψ f S) :
    HasShiftedRationalValue q abv μ (Φ + Ψ) f (R + S) := by
  obtain ⟨⟨a, ha⟩, hR⟩ := hR
  obtain ⟨⟨b, hb⟩, hS⟩ := hS
  refine ⟨⟨max a b, fun s hs =>
    (ha s ((le_max_left a b).trans_lt hs)).add_test
      (hb s ((le_max_right a b).trans_lt hs))⟩, ?_⟩
  exact continuation_of_eq_on_right (continuation_add hR hS)
    ⟨max a b, fun s hs =>
      matrixIntegral_add_test (ha s ((le_max_left a b).trans_lt hs))
        (hb s ((le_max_right a b).trans_lt hs))⟩

/-- Complex scaling in the test variable preserves actual shifted rational
values, including zero scalars. -/
theorem HasShiftedRationalValue.smul_test {q : ℕ} {R : RationalFunctions}
    (hR : HasShiftedRationalValue q abv μ Φ f R) (c : ℂ) :
    HasShiftedRationalValue q abv μ (c • Φ) f (RatFunc.C c * R) := by
  obtain ⟨⟨a, ha⟩, hR⟩ := hR
  refine ⟨⟨a, fun s hs => (ha s hs).smul_test c⟩, ?_⟩
  exact continuation_of_eq_on_right (hasRationalContinuation_const_mul c hR)
    ⟨0, fun _ _ => matrixIntegral_smul_test c⟩

end TestLinearity

section Pairing

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (q : ℕ) (abv : AbsoluteValue F ℝ)
  (μ : Measure (Langlands.GeneralLinear (n + 1) F))
  (C : W →ₗ[ℂ] (Langlands.GeneralLinear (n + 1) F → ℂ))
  (hRat : ∀ (Φ : MatrixTestFunction n F) (w : W),
    ∃ R, HasShiftedRationalValue q abv μ Φ (C w) R)

/-- A chosen actual rational value. Existence is supplied explicitly. -/
def matrixRationalValue (Φ : MatrixTestFunction n F) (w : W) : RationalFunctions :=
  (hRat Φ w).choose

theorem matrixRationalValue_spec (Φ : MatrixTestFunction n F) (w : W) :
    HasShiftedRationalValue q abv μ Φ (C w)
      (matrixRationalValue q abv μ C hRat Φ w) :=
  (hRat Φ w).choose_spec

/-- The unique actual continued matrix integral is complex bilinear in its
full-matrix test and in any linearly parametrized family of coefficients. -/
def matrixRationalPairing (hq : 1 < q) :
    MatrixTestFunction n F →ₗ[ℂ] W →ₗ[ℂ] RationalFunctions where
  toFun Φ :=
    { toFun := matrixRationalValue q abv μ C hRat Φ
      map_add' := by
        intro v w
        apply (matrixRationalValue_spec q abv μ C hRat Φ (v + w)).2.unique hq
        simpa only [map_add] using
          ((matrixRationalValue_spec q abv μ C hRat Φ v).add
            (matrixRationalValue_spec q abv μ C hRat Φ w)).2
      map_smul' := by
        intro c w
        change matrixRationalValue q abv μ C hRat Φ (c • w) =
          c • matrixRationalValue q abv μ C hRat Φ w
        apply (matrixRationalValue_spec q abv μ C hRat Φ (c • w)).2.unique hq
        simpa only [map_smul, RatFunc.smul_eq_C_mul] using
          ((matrixRationalValue_spec q abv μ C hRat Φ w).smul c).2 }
  map_add' := by
    intro Φ Ψ
    ext w
    apply (matrixRationalValue_spec q abv μ C hRat (Φ + Ψ) w).2.unique hq
    exact ((matrixRationalValue_spec q abv μ C hRat Φ w).add_test
      (matrixRationalValue_spec q abv μ C hRat Ψ w)).2
  map_smul' := by
    intro c Φ
    ext w
    change matrixRationalValue q abv μ C hRat (c • Φ) w =
      c • matrixRationalValue q abv μ C hRat Φ w
    apply (matrixRationalValue_spec q abv μ C hRat (c • Φ) w).2.unique hq
    simpa only [RatFunc.smul_eq_C_mul] using
      ((matrixRationalValue_spec q abv μ C hRat Φ w).smul_test c).2

theorem matrixRationalPairing_spec (hq : 1 < q)
    (Φ : MatrixTestFunction n F) (w : W) :
    HasShiftedRationalValue q abv μ Φ (C w)
      (matrixRationalPairing q abv μ C hRat hq Φ w) :=
  matrixRationalValue_spec q abv μ C hRat Φ w

/-- The pairing agrees with every supplied actual continuation. -/
theorem matrixRationalPairing_eq (hq : 1 < q)
    (Φ : MatrixTestFunction n F) (w : W) {R : RationalFunctions}
    (hR : HasShiftedRationalValue q abv μ Φ (C w) R) :
    matrixRationalPairing q abv μ C hRat hq Φ w = R :=
  (matrixRationalPairing_spec q abv μ C hRat hq Φ w).2.unique hq hR.2

end Pairing

section Iota

variable {F : Type uF} [Field F] {n : ℕ}

/-- The literal inverse-transpose coefficient operation as a complex linear
map, for use on the same source coefficient module as the original pairing. -/
def coefficientIotaLinearMap :
    (Langlands.GeneralLinear (n + 1) F → ℂ) →ₗ[ℂ]
      (Langlands.GeneralLinear (n + 1) F → ℂ) where
  toFun := coefficientIota
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coefficientIotaLinearMap_apply
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) :
    coefficientIotaLinearMap f = coefficientIota f := rfl

end Iota

end Langlands.GodementJacquet
