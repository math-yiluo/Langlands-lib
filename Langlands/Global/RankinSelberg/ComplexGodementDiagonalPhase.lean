import Langlands.Global.RankinSelberg.ComplexGodementTriangularIntegral
import Langlands.Representation.Archimedean.ComplexGramFormula
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Diagonal phases in the triangular complex Godement integral -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Operator NNReal ENNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexGramFormula (phaseUnit phaseUnit_val diagonalUnits_phaseUnit_mem)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance diagonalPhaseGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) :=
  borel _
local instance diagonalPhaseGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance diagonalPhaseGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "X" => (UpperEntryPair n → ℂ)

/-- The additive triangular Godement kernel at complex diagonal units. -/
def complexDiagonalKernel (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) (f : G → ℂ)
    (g : Langlands.GeneralLinear (n + 1) ℂ) (a : Fin n → ℂˣ) (k : K) (z : X) : ℂ :=
  Φ (k.val.val * upperTriangularEntries (fun j => (a j : ℂ)) z * trailingRows g.val) *
    (f k.val⁻¹ * (d.character (determinant k.val) : ℂ)) * diagonalTateWeight d ds a

theorem triangularGodementKernel_eq_complexDiagonalKernel (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ)
    (f : G → ℂ) (g : Langlands.GeneralLinear (n + 1) ℂ) (k : K) (y : Fin n → ℝ) (z : X) :
    triangularGodementKernel d ds Φ f g k y z =
      complexDiagonalKernel d ds Φ f g
        (fun j => Units.mk0 (Real.exp (y j) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)))
        k z := rfl

private def phaseEntries (p : Fin n → ℂˣ) (x : X) : X :=
  fun ij => (p ij.1.1 : ℂ) * x ij

private theorem upperTriangularEntries_phase (p a : Fin n → ℂˣ) (z : X) :
    upperTriangularEntries (fun j => ((p * a) j : ℂ)) (phaseEntries p z) =
      (Iwasawa.diagonalUnits p).val * upperTriangularEntries (fun j => (a j : ℂ)) z := by
  ext i j
  rw [Iwasawa.diagonalUnits_val, Matrix.diagonal_mul]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [upperTriangularEntries, hij, phaseEntries]
  · simp [upperTriangularEntries, Pi.mul_apply, Units.val_mul]
  · simp [upperTriangularEntries, not_lt_of_gt hji, ne_of_gt hji]

private theorem unitary_diagonal (p : Fin n → ℂˣ) (hp : ∀ j, ‖(p j : ℂ)‖ = 1) :
    Iwasawa.diagonalUnits p ∈ K := by
  have h (j : Fin n) : phaseUnit (p j) = p j := by
    apply Units.ext
    rw [phaseUnit_val, hp, Complex.ofReal_one, div_one]
  simpa only [h] using diagonalUnits_phaseUnit_mem p

private theorem positionCharacter_mul (ds : List ComplexCharacterData) :
    ∀ (j : ℕ) (p a : ℂˣ), complexPositionCharacter ds j (p * a) =
      complexPositionCharacter ds j p * complexPositionCharacter ds j a := by
  induction ds with
  | nil => intro j p a; simp [complexPositionCharacter]
  | cons d ds ih =>
    intro j p a
    cases j with
    | zero => simp [complexPositionCharacter, map_mul]
    | succ j => exact ih j p a

private theorem determinant_diagonalUnits (p : Fin n → ℂˣ) :
    determinant (Iwasawa.diagonalUnits p) = ∏ j, p j := by
  apply Units.ext
  change (Iwasawa.diagonalUnits p).val.det = Units.coeHom ℂ (∏ j, p j)
  rw [Iwasawa.diagonalUnits_val, Matrix.det_diagonal, map_prod]
  rfl

private theorem diagonalTateWeight_phase (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (p a : Fin n → ℂˣ) (hp : ∀ j, ‖(p j : ℂ)‖ = 1) :
    diagonalTateWeight d ds (p * a) =
      ((d.character (determinant (Iwasawa.diagonalUnits p)) : ℂ) *
        principalSeriesCharacter ℂ n (complexPositionCharacter ds) (fun j => (p j)⁻¹)) *
      diagonalTateWeight d ds a := by
  have hd : (d.character (∏ j, p j) : ℂ) = ∏ j, (d.character (p j) : ℂ) :=
    map_prod ((Units.coeHom ℂ).comp d.character.toMonoidHom) p Finset.univ
  rw [determinant_diagonalUnits, hd, principalSeriesCharacter, diagonalTateWeight,
    diagonalTateWeight, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hpinv : ‖((p j)⁻¹ : ℂˣ).val‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hp, inv_one]
  have hnorm : normPower 1 (p j) = 1 := by
    change ((‖(p j : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (1 : ℂ) = 1
    rw [hp, one_pow, Complex.ofReal_one, Complex.one_cpow]
  simp only [Pi.mul_apply, map_mul, Units.val_mul, mul_inv_rev, positionCharacter_mul,
    hnorm, one_mul, hpinv, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]
  ring

private theorem phase_mul_preserving (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) :
    MeasurePreserving ((u : ℂ) * ·) (volume : Measure ℂ) volume := by
  let E : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { toLinearEquiv := (LinearEquiv.smulOfNeZero ℂ ℂ (u : ℂ) u.ne_zero).restrictScalars ℝ
      norm_map' := fun z => by
        change ‖(u : ℂ) * z‖ = ‖z‖
        rw [norm_mul, hu, one_mul] }
  exact E.measurePreserving

private theorem phaseEntries_preserving (p : Fin n → ℂˣ) (hp : ∀ j, ‖(p j : ℂ)‖ = 1) :
    MeasurePreserving (phaseEntries p) (volume : Measure X) volume := by
  have h (ij : UpperEntryPair n) := phase_mul_preserving (p ij.1.1) (hp ij.1.1)
  refine ⟨Measurable.of_eval (fun ij => (h ij).measurable.comp (measurable_pi_apply ij)), ?_⟩
  change (Measure.pi (fun _ : UpperEntryPair n => (volume : Measure ℂ))).map
      (fun (x : X) ij => (p ij.1.1 : ℂ) * x ij) = Measure.pi (fun _ => (volume : Measure ℂ))
  have hfinite (ij : UpperEntryPair n) : SigmaFinite ((volume : Measure ℂ).map ((p ij.1.1 : ℂ) * ·)) := by
    rw [(h ij).map_eq]
    infer_instance
  rw [Measure.pi_map_pi (hμ := hfinite) (fun ij => (h ij).measurable.aemeasurable)]
  simp_rw [(h _).map_eq]

private theorem complexDiagonalKernel_phase (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ)
    {f : G → ℂ} (hf : f ∈ complexStandardModule n ds) (g : Langlands.GeneralLinear (n + 1) ℂ)
    (p a : Fin n → ℂˣ) (hp : ∀ j, ‖(p j : ℂ)‖ = 1) (k : K) (z : X) :
    complexDiagonalKernel d ds Φ f g (p * a) k (phaseEntries p z) =
    complexDiagonalKernel d ds Φ f g a (k * ⟨Iwasawa.diagonalUnits p, unitary_diagonal p hp⟩) z := by
  let t : K := ⟨Iwasawa.diagonalUnits p, unitary_diagonal p hp⟩
  have hf' : f (k * t).val⁻¹ =
      principalSeriesCharacter ℂ n (complexPositionCharacter ds) (fun j => (p j)⁻¹) * f k.val⁻¹ := by
    change f (k.val * Iwasawa.diagonalUnits p)⁻¹ = _
    rw [mul_inv_rev, ← map_inv]
    change f (Iwasawa.diagonalUnits (fun j => (p j)⁻¹) * k.val⁻¹) = _
    simpa only [OneMemClass.coe_one, mul_one] using hf.2 (fun j => (p j)⁻¹) 1 k.val⁻¹
  change complexDiagonalKernel d ds Φ f g (p * a) k (phaseEntries p z) =
    complexDiagonalKernel d ds Φ f g a (k * t) z
  rw [complexDiagonalKernel, complexDiagonalKernel, upperTriangularEntries_phase, hf',
    diagonalTateWeight_phase d ds p a hp]
  change _ = Φ (((k.val * Iwasawa.diagonalUnits p).val) * upperTriangularEntries (fun j => (a j : ℂ)) z *
    trailingRows g.val) * (_ * (d.character (determinant (k.val * Iwasawa.diagonalUnits p)) : ℂ)) * _
  simp only [Units.val_mul, mul_assoc, map_mul]
  ring

private theorem continuous_complexDiagonalKernel (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) {Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ}
    (hΦ : Continuous Φ) (f : G → ℂ) (g : Langlands.GeneralLinear (n + 1) ℂ)
    (a : Fin n → ℂˣ) (k : K) : Continuous (complexDiagonalKernel d ds Φ f g a k) := by
  have hB : Continuous (upperTriangularEntries (fun j => (a j : ℂ))) := by
    apply continuous_matrix
    intro i j
    by_cases h : i < j
    · simp only [upperTriangularEntries, dite_eq_left h]
      exact continuous_apply (⟨(i, j), h⟩ : UpperEntryPair n)
    · simp only [upperTriangularEntries, dite_eq_right h]
      exact continuous_const
  have hT : Continuous (fun z : X => k.val.val *
      upperTriangularEntries (fun j => (a j : ℂ)) z * trailingRows g.val) :=
    (continuous_const.matrix_mul hB).matrix_mul continuous_const
  exact ((hΦ.comp hT).mul continuous_const).mul continuous_const

/-- The compact and strictly upper integrals of the weighted complex diagonal kernel depend
only on the positive diagonal moduli. -/
theorem integral_complexDiagonalKernel_phase (κ : Measure K) [κ.IsMulRightInvariant]
    (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    {Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ} (hΦ : Continuous Φ)
    {f : G → ℂ} (hf : f ∈ complexStandardModule n ds) (g : Langlands.GeneralLinear (n + 1) ℂ)
    (p a : Fin n → ℂˣ) (hp : ∀ j, ‖(p j : ℂ)‖ = 1) :
    (∫ k, (∫ z, complexDiagonalKernel d ds Φ f g (p * a) k z) ∂κ) =
      ∫ k, (∫ z, complexDiagonalKernel d ds Φ f g a k z) ∂κ := by
  let t : K := ⟨Iwasawa.diagonalUnits p, unitary_diagonal p hp⟩
  calc
    _ = ∫ k, (∫ z, complexDiagonalKernel d ds Φ f g a (k * t) z) ∂κ := by
      apply integral_congr_ae
      filter_upwards [] with k
      let F := complexDiagonalKernel d ds Φ f g (p * a) k
      have he := phaseEntries_preserving p hp
      have hm : Continuous F := continuous_complexDiagonalKernel d ds hΦ f g (p * a) k
      have h : (∫ z, F z ∂(volume : Measure X).map (phaseEntries p)) =
          ∫ z : X, F (phaseEntries p z) :=
        integral_map he.measurable.aemeasurable hm.aestronglyMeasurable
      rw [he.map_eq] at h
      change (∫ z : X, F z) = _
      rw [h]
      apply integral_congr_ae
      filter_upwards [] with z
      exact complexDiagonalKernel_phase d ds Φ hf g p a hp k z
    _ = _ := (measurePreserving_mul_right κ t).integral_comp (measurableEmbedding_mulRight t)
      (fun k : K => ∫ z : X, complexDiagonalKernel d ds Φ f g a k z)

/-- The same phase change preserves the iterated absolute integral, including its finiteness. -/
theorem lintegral_enorm_complexDiagonalKernel_phase (κ : Measure K) [κ.IsMulRightInvariant]
    (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    {Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ} (hΦ : Continuous Φ)
    {f : G → ℂ} (hf : f ∈ complexStandardModule n ds) (g : Langlands.GeneralLinear (n + 1) ℂ)
    (p a : Fin n → ℂˣ) (hp : ∀ j, ‖(p j : ℂ)‖ = 1) :
    (∫⁻ k, (∫⁻ z, ‖complexDiagonalKernel d ds Φ f g (p * a) k z‖ₑ) ∂κ) =
      ∫⁻ k, (∫⁻ z, ‖complexDiagonalKernel d ds Φ f g a k z‖ₑ) ∂κ := by
  let t : K := ⟨Iwasawa.diagonalUnits p, unitary_diagonal p hp⟩
  calc
    _ = ∫⁻ k, (∫⁻ z, ‖complexDiagonalKernel d ds Φ f g a (k * t) z‖ₑ) ∂κ := by
      apply lintegral_congr
      intro k
      let F := complexDiagonalKernel d ds Φ f g (p * a) k
      have hm : Continuous F := continuous_complexDiagonalKernel d ds hΦ f g (p * a) k
      change (∫⁻ z : X, ‖F z‖ₑ) = _
      rw [← (phaseEntries_preserving p hp).lintegral_comp hm.measurable.enorm]
      apply lintegral_congr
      intro z
      exact congrArg enorm (complexDiagonalKernel_phase d ds Φ hf g p a hp k z)
    _ = _ := (measurePreserving_mul_right κ t).lintegral_comp_emb (measurableEmbedding_mulRight t)
      (fun k : K => ∫⁻ z : X, ‖complexDiagonalKernel d ds Φ f g a k z‖ₑ)

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
