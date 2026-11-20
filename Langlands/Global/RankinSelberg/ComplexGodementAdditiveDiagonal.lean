import Langlands.Global.RankinSelberg.ComplexGodementGroupDiagonal
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity
import Mathlib.MeasureTheory.Integral.Pi

/-! # The Godement kernel with additive Tate weights -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Operator NNReal ENNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance additiveDiagonalGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _

private def normDensity (z : ℂ) : ℝ≥0 := (‖z‖₊ ^ 2)⁻¹

private theorem measurable_normDensity : Measurable normDensity :=
  (continuous_nnnorm.measurable.pow_const 2).inv

private theorem multiplicativeComplexLebesgue_eq : multiplicativeComplexLebesgue =
    (volume : Measure ℂ).withDensity (fun z => (normDensity z : ℝ≥0∞)) := by
  change (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ 2)⁻¹) = _
  congr 1
  funext z
  rw [← ENNReal.ofReal_coe_nnreal]
  rfl

private def diagonalDensity {n : ℕ} (z : Fin n → ℂ) : ℝ≥0 := ∏ j, normDensity (z j)

private theorem measurable_diagonalDensity {n : ℕ} : Measurable (diagonalDensity (n := n)) :=
  Finset.measurable_prod _ fun j _ => measurable_normDensity.comp (measurable_pi_apply j)

private theorem pi_multiplicativeComplexLebesgue (n : ℕ) :
    Measure.pi (fun _ : Fin n => multiplicativeComplexLebesgue) =
      (volume : Measure (Fin n → ℂ)).withDensity (fun z => (diagonalDensity z : ℝ≥0∞)) := by
  induction n with
  | zero =>
    have h : (fun z : Fin 0 → ℂ => (diagonalDensity z : ℝ≥0∞)) = 1 := by
      funext z
      simp [diagonalDensity]
    rw [h, withDensity_one, volume_pi]
    exact Measure.pi_eq fun s _ => by rw [Measure.pi_pi]; simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
    have hleft := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) =>
      multiplicativeComplexLebesgue) 0).map_eq
    have hright := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).map_eq
    apply e.measurableEmbedding.map_injective
    rw [show Measure.map e (Measure.pi (fun _ : Fin (n + 1) => multiplicativeComplexLebesgue)) =
        multiplicativeComplexLebesgue.prod (Measure.pi (fun _ : Fin n => multiplicativeComplexLebesgue))
      from hleft]
    rw [Langlands.RankinSelberg.GLDeterminantDensity.map_withDensity_equiv,
      show Measure.map e (volume : Measure (Fin (n + 1) → ℂ)) =
        (volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ)) from hright,
      ih, multiplicativeComplexLebesgue_eq, prod_withDensity
        measurable_normDensity.coe_nnreal_ennreal measurable_diagonalDensity.coe_nnreal_ennreal]
    congr 1
    funext p
    simp only [diagonalDensity, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero, ENNReal.coe_mul]

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Z" => (Fin n → ℂ)
local notation "X" => (UpperEntryPair n → ℂ)

/-- The scalar Tate weight for additive Lebesgue measure, with value zero when `z = 0`. -/
def scalarAdditiveTateWeight (d e : ComplexCharacterData) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (z / (‖z‖ : ℂ)) ^ (d.weight - e.weight) *
    (‖z‖ : ℂ) ^ (2 * (d.exponent - e.exponent + 1) - 2)

/-- The factor of the additive diagonal kernel that is independent of the diagonal Tate weights. -/
def diagonalTestKernel (d : ComplexCharacterData)
    (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) (f : G → ℂ)
    (g : Langlands.GeneralLinear (n + 1) ℂ) (a : Z) (k : K) (z : X) : ℂ :=
  Φ (k.val.val * upperTriangularEntries a z * trailingRows g.val) *
    (f k.val⁻¹ * (d.character (determinant k.val) : ℂ))

/-- The Godement diagonal kernel relative to additive Lebesgue measure in the diagonal. -/
def additiveDiagonalKernel (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData)
    (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) (f : G → ℂ)
    (g : Langlands.GeneralLinear (n + 1) ℂ) (a : Z) (k : K) (z : X) : ℂ :=
  diagonalTestKernel d Φ f g a k z * ∏ j, scalarAdditiveTateWeight d (es j) (a j)

private theorem density_smul_multiplicativeDiagonalKernel (d : ComplexCharacterData)
    (es : Fin n → ComplexCharacterData) (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ)
    (f : G → ℂ) (g : Langlands.GeneralLinear (n + 1) ℂ) (a : Z) (k : K) (z : X) :
    diagonalDensity a • multiplicativeDiagonalKernel d (List.ofFn es) Φ f g a k z =
      additiveDiagonalKernel d es Φ f g a k z := by
  by_cases ha : ∀ j, a j ≠ 0
  · let au (j : Fin n) := Units.mk0 (a j) (ha j)
    have H : multiplicativeDiagonalKernel d (List.ofFn es) Φ f g a k z =
        complexDiagonalKernel d (List.ofFn es) Φ f g au k z := by
      unfold multiplicativeDiagonalKernel
      congr 1
      funext j
      change (if h : a j = 0 then 1 else Units.mk0 (a j) h) = au j
      rw [dite_eq_right (ha j)]
    rw [H]
    change diagonalDensity a • (diagonalTestKernel d Φ f g a k z *
      diagonalTateWeight d (List.ofFn es) au) = _
    have hD : ((diagonalDensity a : ℝ) : ℂ) = ∏ j, (((‖(au j : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
      unfold diagonalDensity
      rw [NNReal.coe_prod, Complex.ofReal_prod]
      rfl
    rw [NNReal.smul_def, Complex.real_smul, hD, mul_left_comm, diagonalTateWeight_mul_density]
    simp only [additiveDiagonalKernel, scalarAdditiveTateWeight, ite_eq_right (ha _)]
    rfl
  · push Not at ha
    obtain ⟨j, hj⟩ := ha
    have hD : diagonalDensity a = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [normDensity, hj])
    have hT : ∏ i, scalarAdditiveTateWeight d (es i) (a i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [scalarAdditiveTateWeight, hj])
    rw [hD, zero_smul, additiveDiagonalKernel, hT, mul_zero]

/-- The complex multiplicative integral turns into the additive Tate integral by multiplying
with the product of inverse squared norm densities. -/
theorem multiplicativeDiagonal_eq_additive (κ : Measure K) [SFinite κ]
    (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData)
    (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) (f : G → ℂ)
    (g : Langlands.GeneralLinear (n + 1) ℂ) :
    let η := κ.prod (volume : Measure X)
    let ρ := Measure.pi (fun _ : Fin n => multiplicativeComplexLebesgue)
    let B (p : Z × (K × X)) := multiplicativeDiagonalKernel d (List.ofFn es) Φ f g p.1 p.2.1 p.2.2
    let A (p : Z × (K × X)) := additiveDiagonalKernel d es Φ f g p.1 p.2.1 p.2.2
    (Integrable B (ρ.prod η) ↔ Integrable A (volume.prod η)) ∧
      (∫ p, B p ∂ρ.prod η) = ∫ p, A p ∂volume.prod η := by
  intro η ρ B A
  have hρ : ρ.prod η = (volume.prod η).withDensity
      (fun p : Z × (K × X) => (diagonalDensity p.1 : ℝ≥0∞)) := by
    change (Measure.pi (fun _ : Fin n => multiplicativeComplexLebesgue)).prod η = _
    rw [pi_multiplicativeComplexLebesgue, prod_withDensity_left measurable_diagonalDensity.coe_nnreal_ennreal]
  have hM : Measurable (fun p : Z × (K × X) => diagonalDensity p.1) :=
    measurable_diagonalDensity.comp measurable_fst
  have hA : (fun p : Z × (K × X) => diagonalDensity p.1 • B p) = A :=
    funext fun p => density_smul_multiplicativeDiagonalKernel d es Φ f g p.1 p.2.1 p.2.2
  rw [hρ, integrable_withDensity_iff_integrable_smul hM, integral_withDensity_eq_integral_smul hM, hA]
  exact ⟨Iff.rfl, rfl⟩

/-- The Godement group integral in additive diagonal and strictly upper entries, with one
scalar Tate factor per diagonal position. -/
def ComplexGodementAdditiveDiagonalStatement : Prop :=
  ∀ (μ : Measure G) (κ : Measure K), μ.IsHaarMeasure → μ.IsMulRightInvariant → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData)
      (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) (f : G → ℂ),
      Continuous Φ → f ∈ complexStandardModule n (List.ofFn es) →
      ∀ g : Langlands.GeneralLinear (n + 1) ℂ,
        let η := (volume : Measure Z).prod (κ.prod (volume : Measure X))
        let I := godementSectionIntegrand d Φ f g
        let A (p : Z × (K × X)) := additiveDiagonalKernel d es Φ f g p.1 p.2.1 p.2.2
        (Integrable I μ ↔ Integrable A η) ∧
          (Integrable I μ → (∫ h, I h ∂μ) = (c : ℂ) * ∫ p, A p ∂η)

theorem complexGodementAdditiveDiagonal : ComplexGodementAdditiveDiagonalStatement (n := n) := by
  intro μ κ hμ hright hκ
  let : κ.IsHaarMeasure := hκ
  obtain ⟨c, hc, h⟩ := complexGodementGroupDiagonal (n := n) μ κ hμ hright hκ
  refine ⟨c, hc, ?_⟩
  intro d es Φ f hΦ hf g η I A
  obtain ⟨hi, he⟩ := h d (List.ofFn es) Φ f hΦ hf g
  obtain ⟨hi', he'⟩ := multiplicativeDiagonal_eq_additive κ d es Φ f g
  exact ⟨hi.trans hi', fun hI => (he hI).trans (congrArg ((c : ℂ) * ·) he')⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
