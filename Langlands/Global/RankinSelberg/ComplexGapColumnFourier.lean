import Langlands.Global.RankinSelberg.ComplexGodementColumnChange
import Langlands.Global.RankinSelberg.ComplexGodementFourier
import Mathlib.MeasureTheory.Integral.Pi

/-! # The affine column Fourier transfer in the larger-gap unfolding -/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapColumnFourier

open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGodementColumnChange (integral_mulVec)
open Langlands.Archimedean.ComplexPartialJacquet (vecMulLinearEquiv)
open ComplexGodementFourier (merge merge_apply_left merge_apply_right continuous_merge
  norm_le_norm_merge_left norm_le_norm_merge_right integral_merge_left_eq piMeasure
  piMeasure_neg fourier psi exists_schwartz_fourier integrable_of_norm_le_schwartz continuous_psi norm_psi)

variable {r : ℕ}
local notation "V" => Fin (r + 1) → ℂ
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ

private def columnCLE (g : G) : V ≃L[ℝ] V :=
  let e := vecMulLinearEquiv (B := g.val.transpose) (Matrix.det_transpose g.val ▸ g.det_ne_zero)
  (e.restrictScalars ℝ).toContinuousLinearEquiv

private theorem columnCLE_apply (g : G) (x : V) : columnCLE g x = g.val.mulVec x :=
  Matrix.vecMul_transpose g.val x

/-- Pull back a column Schwartz function by matrix multiplication. -/
def pullColumn (g : G) (Φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (columnCLE g) Φ

@[simp]
theorem pullColumn_apply (g : G) (Φ : 𝓢(V, ℂ)) (x : V) :
    pullColumn g Φ x = Φ (g.val.mulVec x) :=
  congrArg Φ (columnCLE_apply g x)

/-- Full column Fourier transformation moves a matrix to the inverse transpose
and contributes its additive determinant Jacobian. -/
theorem fourier_pullColumn (a : ℂˣ) (g : G) (Φ : 𝓢(V, ℂ)) (y : V) :
    fourier a (pullColumn g Φ) y =
      ((complexNormalizedAbs g.val.det)⁻¹ : ℝ) •
        fourier a Φ (g⁻¹.val.transpose.mulVec y) := by
  let z := g⁻¹.val.transpose.mulVec y
  let K (x : V) := Φ x * psi a (∑ i, x i * z i)
  have hp (x : V) : (∑ i, g.val.mulVec x i * z i) = ∑ i, x i * y i := by
    change dotProduct (g.val.mulVec x) (g⁻¹.val.transpose.mulVec y) = dotProduct x y
    rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
      dotProduct_comm]
  calc
    fourier a (pullColumn g Φ) y = ∫ x, K (g.val.mulVec x) ∂piMeasure _ a := by
      simp only [ComplexGodementFourier.fourier, pullColumn_apply, K, hp]
    _ = ((complexNormalizedAbs g.val.det)⁻¹ : ℝ) • ∫ x, K x ∂piMeasure _ a :=
      integral_mulVec _ g K
    _ = _ := rfl

variable (p : Fin (r + 1) → Prop) [DecidablePred p]

local notation "U" => {i : Fin (r + 1) // p i} → ℂ
local notation "L" => {i : Fin (r + 1) // ¬ p i} → ℂ

/-- Fourier exchange between complementary affine column slices after an
arbitrary invertible complex change of coordinates. -/
def ComplexGapColumnFourierStatement : Prop :=
  ∀ (a : ℂˣ) (g : G) (Φ : 𝓢(V, ℂ)) (α : U) (β : L),
    let P (x : U) := Φ (g.val.mulVec (merge p x β)) * psi a (∑ i, x i * α i)
    let Q (y : L) := fourier a Φ (g⁻¹.val.transpose.mulVec (merge p α y)) *
      psi (-a) (∑ i, y i * β i)
    Integrable P (piMeasure _ a) ∧ Integrable Q (piMeasure _ a) ∧
    (∫ x, P x ∂piMeasure _ a) =
      ((complexNormalizedAbs g.val.det)⁻¹ : ℝ) • ∫ y, Q y ∂piMeasure _ a

theorem complexGapColumnFourier : ComplexGapColumnFourierStatement (r := r) p := by
  intro a g Φ α β
  let P (x : U) := pullColumn g Φ (merge p x β) * psi a (∑ i, x i * α i)
  let Q (y : L) := fourier a Φ (g⁻¹.val.transpose.mulVec (merge p α y)) *
    psi (-a) (∑ i, y i * β i)
  have hI : Integrable P (piMeasure _ a) := by
    apply integrable_of_norm_le_schwartz _ (pullColumn g Φ) (g := fun x => merge p x β)
    · exact ((pullColumn g Φ).continuous.comp ((continuous_merge p).comp
          (continuous_id.prodMk continuous_const))).mul
          ((continuous_psi a).comp (by fun_prop)) |>.aestronglyMeasurable
    · exact fun x => norm_le_norm_merge_left p x β
    · intro x
      simp only [P, norm_mul, norm_psi, mul_one]
      exact le_rfl
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz_fourier a Φ
  let gᵢ := Langlands.GeneralLinear.inverseTranspose (r + 1) ℂ g
  have hQ (y : L) : Q y = pullColumn gᵢ Ψ (merge p α y) * psi (-a) (∑ i, y i * β i) := by
    simp only [Q, pullColumn_apply, hΨ]
    rfl
  have hId : Integrable Q (piMeasure _ a) := by
    apply integrable_of_norm_le_schwartz _ (pullColumn gᵢ Ψ) (g := fun y => merge p α y)
    · rw [funext hQ]
      exact ((pullColumn gᵢ Ψ).continuous.comp ((continuous_merge p).comp
          (continuous_const.prodMk continuous_id))).mul
          ((continuous_psi (-a)).comp (by fun_prop)) |>.aestronglyMeasurable
    · exact fun y => norm_le_norm_merge_right p α y
    · intro y
      simp only [hQ, norm_mul, norm_psi, mul_one]
      exact le_rfl
  simp only [pullColumn_apply, P] at hI
  refine ⟨hI, hId, ?_⟩
  have h := integral_merge_left_eq (p := p) (-a) (pullColumn g Φ) α β
  simp only [neg_neg, piMeasure_neg, fourier_pullColumn, smul_mul_assoc, integral_smul, pullColumn_apply] at h
  exact h

/-- Independent column slices can be transferred at once. Each contributes the same
determinant factor for the matrix used in all columns. -/
theorem complexGapColumnFourierProduct {J : Type*} [Fintype J]
    (part : J → Fin (r + 1) → Prop) [∀ j, DecidablePred (part j)]
    (a : ℂˣ) (g : G) (Φ : J → 𝓢(V, ℂ))
    (α : ∀ j, {i // part j i} → ℂ) (β : ∀ j, {i // ¬ part j i} → ℂ) :
    let P (j : J) (x : {i // part j i} → ℂ) :=
      Φ j (g.val.mulVec (merge (part j) x (β j))) * psi a (∑ i, x i * α j i)
    let Q (j : J) (y : {i // ¬ part j i} → ℂ) :=
      fourier a (Φ j) (g⁻¹.val.transpose.mulVec (merge (part j) (α j) y)) *
        psi (-a) (∑ i, y i * β j i)
    Integrable (fun x => ∏ j, P j (x j)) (Measure.pi fun j : J => piMeasure {i // part j i} a) ∧
    Integrable (fun y => ∏ j, Q j (y j)) (Measure.pi fun j : J => piMeasure {i // ¬ part j i} a) ∧
    (∫ x, ∏ j, P j (x j) ∂Measure.pi fun j : J => piMeasure {i // part j i} a) =
      (((complexNormalizedAbs g.val.det)⁻¹ : ℝ) : ℂ) ^ Fintype.card J *
        ∫ y, ∏ j, Q j (y j) ∂Measure.pi fun j : J => piMeasure {i // ¬ part j i} a := by
  intro P Q
  have h j := complexGapColumnFourier (part j) a g (Φ j) (α j) (β j)
  refine ⟨Integrable.fintype_prod_dep (fun j => (h j).1),
    Integrable.fintype_prod_dep (fun j => (h j).2.1), ?_⟩
  rw [integral_fintype_prod_eq_prod P, integral_fintype_prod_eq_prod Q]
  have hIntegral (j : J) : (∫ x, P j x ∂piMeasure {i // part j i} a) =
      ((complexNormalizedAbs g.val.det)⁻¹ : ℝ) • ∫ y, Q j y ∂piMeasure {i // ¬ part j i} a :=
    (h j).2.2
  simp_rw [hIntegral, Complex.real_smul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end Langlands.Global.RankinSelbergGlobal.ComplexGapColumnFourier
