import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-!
# Pointwise norm data on the left-unipotent quotient

These derived constructions supply the determinant absolute value, last row and
Whittaker norms appearing in JPSS Section 8.3. They assert no integrability or
analytic estimate.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F]

/-- The determinant absolute value is invariant under left unipotent multiplication. -/
theorem determinantAbs_unipotent_mul (abv : AbsoluteValue F ℝ) {n : ℕ}
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F) :
    abv (Matrix.det (u.val * g).val) = abv (Matrix.det g.val) := by
  simp [Matrix.det_mul]

/-- The actual determinant absolute value on `N_(n+1) \ GL_(n+1)`. -/
def quotientDeterminantAbs (abv : AbsoluteValue F ℝ) (n : ℕ) :
    LeftUnipotentQuotient n F → ℝ :=
  QuotientIntegration.descend _ (fun g => abv (Matrix.det g.val))
    (determinantAbs_unipotent_mul abv)

@[simp] theorem quotientDeterminantAbs_mk (abv : AbsoluteValue F ℝ) (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    quotientDeterminantAbs abv n (Quotient.mk _ g) = abv (Matrix.det g.val) := rfl

theorem quotientDeterminantAbs_nonneg (abv : AbsoluteValue F ℝ) (n : ℕ)
    (q : LeftUnipotentQuotient n F) : 0 ≤ quotientDeterminantAbs abv n q := by
  induction q using Quotient.inductionOn with
  | h g => exact abv.nonneg _

/-- Invertibility makes the determinant absolute value strictly positive. -/
theorem quotientDeterminantAbs_pos (abv : AbsoluteValue F ℝ) (n : ℕ)
    (q : LeftUnipotentQuotient n F) : 0 < quotientDeterminantAbs abv n q := by
  induction q using Quotient.inductionOn with
  | h g => exact abv.pos (Matrix.GeneralLinearGroup.det_ne_zero g)

/-- The actual last row on the left-unipotent quotient. -/
def quotientLastRow (n : ℕ) : LeftUnipotentQuotient n F → (Fin (n + 1) → F) :=
  QuotientIntegration.descend _ lastRow lastRow_unipotent_mul

@[simp] theorem quotientLastRow_mk (n : ℕ) (g : Langlands.GeneralLinear (n + 1) F) :
    quotientLastRow n (Quotient.mk _ g) = lastRow g := rfl

section WhittakerNorms

variable [TopologicalSpace F]

/-- Unitarity removes the standard Whittaker character after taking the norm. -/
theorem whittakerNorm_invariant (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W : WhittakerFunctions ψ n) (u : upperUnipotent (n + 1) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    ‖W.val (u.val * g)‖ = ‖W.val g‖ := by
  rw [W.property, norm_mul, norm_standardCharacter, one_mul]

/-- The norm of any standard Whittaker function, descended to the actual quotient. -/
def whittakerNorm (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W : WhittakerFunctions ψ n) : LeftUnipotentQuotient n F → ℝ :=
  QuotientIntegration.descend _ (fun g => ‖W.val g‖) (whittakerNorm_invariant ψ W)

@[simp] theorem whittakerNorm_mk (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W : WhittakerFunctions ψ n) (g : Langlands.GeneralLinear (n + 1) F) :
    whittakerNorm ψ W (Quotient.mk _ g) = ‖W.val g‖ := rfl

theorem whittakerNorm_nonneg (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W : WhittakerFunctions ψ n) (q : LeftUnipotentQuotient n F) :
    0 ≤ whittakerNorm ψ W q := by
  induction q using Quotient.inductionOn with
  | h g => exact norm_nonneg _

@[simp] theorem whittakerNorm_zero (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (q : LeftUnipotentQuotient n F) :
    whittakerNorm ψ (0 : WhittakerFunctions ψ n) q = 0 := by
  induction q using Quotient.inductionOn with
  | h g => change ‖(0 : ℂ)‖ = 0; exact norm_zero

/-- The inverse standard character is also removed by the norm. -/
theorem inverseWhittakerNorm_invariant (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W' : InverseWhittakerFunctions ψ n) (u : upperUnipotent (n + 1) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    ‖W'.val (u.val * g)‖ = ‖W'.val g‖ := by
  rw [W'.property, norm_mul, inverseStandardCharacter_apply, norm_inv,
    ψ.norm_complex, inv_one, one_mul]

/-- The norm of any inverse-character Whittaker function on the actual quotient. -/
def inverseWhittakerNorm (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W' : InverseWhittakerFunctions ψ n) : LeftUnipotentQuotient n F → ℝ :=
  QuotientIntegration.descend _ (fun g => ‖W'.val g‖)
    (inverseWhittakerNorm_invariant ψ W')

@[simp] theorem inverseWhittakerNorm_mk (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W' : InverseWhittakerFunctions ψ n) (g : Langlands.GeneralLinear (n + 1) F) :
    inverseWhittakerNorm ψ W' (Quotient.mk _ g) = ‖W'.val g‖ := rfl

theorem inverseWhittakerNorm_nonneg (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (W' : InverseWhittakerFunctions ψ n) (q : LeftUnipotentQuotient n F) :
    0 ≤ inverseWhittakerNorm ψ W' q := by
  induction q using Quotient.inductionOn with
  | h g => exact norm_nonneg _

@[simp] theorem inverseWhittakerNorm_zero (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (q : LeftUnipotentQuotient n F) :
    inverseWhittakerNorm ψ (0 : InverseWhittakerFunctions ψ n) q = 0 := by
  induction q using Quotient.inductionOn with
  | h g => change ‖(0 : ℂ)‖ = 0; exact norm_zero

/-- Adjoining the final identity block preserves norm invariance on the small group. -/
theorem restrictedWhittakerNorm_invariant (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (k : ℕ) (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F) :
    ‖W.val (appendIdentity n (0 + k + 1) (u.val * g))‖ =
      ‖W.val (appendIdentity n (0 + k + 1) g)‖ := by
  simpa only [appendUnipotent_val, map_mul] using
    whittakerNorm_invariant ψ W (appendUnipotent u (0 + k + 1))
      (appendIdentity n (0 + k + 1) g)

/-- The restricted norm for the exact zero-row unequal-rank parameterization.
The large Whittaker index is kept as `n + (0 + k + 1)`. -/
def restrictedWhittakerNorm (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (k : ℕ) (W : WhittakerFunctions ψ (n + (0 + k + 1))) :
    LeftUnipotentQuotient n F → ℝ :=
  QuotientIntegration.descend _ (fun g => ‖W.val (appendIdentity n (0 + k + 1) g)‖)
    (restrictedWhittakerNorm_invariant ψ k W)

@[simp] theorem restrictedWhittakerNorm_mk (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (k : ℕ) (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (g : Langlands.GeneralLinear (n + 1) F) :
    restrictedWhittakerNorm ψ k W (Quotient.mk _ g) =
      ‖W.val (appendIdentity n (0 + k + 1) g)‖ := rfl

theorem restrictedWhittakerNorm_nonneg (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (k : ℕ) (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (q : LeftUnipotentQuotient n F) : 0 ≤ restrictedWhittakerNorm ψ k W q := by
  induction q using Quotient.inductionOn with
  | h g => exact norm_nonneg _

@[simp] theorem restrictedWhittakerNorm_zero (ψ : UnitaryAdditiveCharacter F)
    (n k : ℕ) (q : LeftUnipotentQuotient n F) :
    restrictedWhittakerNorm ψ k (0 : WhittakerFunctions ψ (n + (0 + k + 1))) q = 0 := by
  induction q using Quotient.inductionOn with
  | h g => change ‖(0 : ℂ)‖ = 0; exact norm_zero

end WhittakerNorms

end Langlands.RankinSelberg
