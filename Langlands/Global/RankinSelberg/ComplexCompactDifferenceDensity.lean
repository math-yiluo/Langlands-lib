import Langlands.Global.RankinSelberg.ComplexCentralPolynomialWeight
import Langlands.Global.RankinSelberg.ComplexCompactSmoothDifferences

/-! # Compact-finite approximation in the complex compact difference bounds -/

noncomputable section

open MeasureTheory Set
open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexCompactDifferenceDensity

open Langlands.Archimedean (complexPositionCharacter complexStandardModule continuous_unitary_toUnits
  complexPrincipalSeriesExtension principalSeriesCharacter)
open Langlands.Archimedean.ComplexDuality (exists_diagonalUnits_mul_upperUnipotent_mul_unitary)
open Langlands.Archimedean.ComplexGramFormula (phaseUnit)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (phaseMatrix phaseMatrix_val)
open Langlands.Archimedean.UnitaryFinitePolynomial (polynomialStar polynomialStar_toSubalgebra
  inv_mul_mem_separated separated translateSpan)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCentralPolynomialWeight (complexCentralPolynomialWeight)
open ComplexCompactDifferences (displacementProduct displacementProduct_nonneg)
open ComplexCompactSmoothDifferences (compactFunctionDifference CompactProfileDifferenceBound)
open ComplexGodement (compactMatrixHaar)

local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Std" => Automorphic.complexStandardKFinite

local instance compactDifferenceDensityMeasurable (n : ℕ) : MeasurableSpace (K n) := borel _
local instance compactDifferenceDensityBorel (n : ℕ) : BorelSpace (K n) := ⟨rfl⟩

variable {n : ℕ}
local notation "νK" => compactMatrixHaar n

private theorem integrable_compact {E : Type*} [NormedAddCommGroup E] {F : K n → E}
    (hF : Continuous F) : Integrable F νK :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Right compact convolution on the unitary matrix group. -/
def convolution (w : C(K n, ℂ)) (φ : K n → ℂ) (x : K n) : ℂ :=
  ∫ k, w k * φ (x * k) ∂νK

private theorem continuous_convolution (w : C(K n, ℂ)) {φ : K n → ℂ} (hφ : Continuous φ) :
    Continuous (convolution w φ) := by
  have hc : Continuous (Function.uncurry (fun (x k : K n) => w k * φ (x * k))) :=
    (w.continuous.comp continuous_snd).mul (hφ.comp (continuous_fst.mul continuous_snd))
  change Continuous (fun x : K n => ∫ k, w k * φ (x * k) ∂νK)
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous (μ := νK) hc isCompact_univ

private theorem convolution_finite {w : C(K n, ℂ)} (hw : w ∈ polynomialStar n)
    {φ : K n → ℂ} (hφ : Continuous φ) : FiniteDimensional ℂ (translateSpan (convolution w φ)) := by
  have hp : w ∈ (polynomialStar n).toSubalgebra := hw
  rw [polynomialStar_toSubalgebra] at hp
  have hsep := inv_mul_mem_separated hp
  rw [separated] at hsep
  obtain ⟨m, c, s, hs⟩ := Submodule.mem_span_set'.mp hsep
  choose α _ β hβ using fun i => (s i).property
  let F (i : Fin m) := convolution (β i) φ
  have hV : FiniteDimensional ℂ (Submodule.span ℂ (range F)) :=
    FiniteDimensional.span_of_finite ℂ (finite_range F)
  apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (range F))
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  have hrep (k : K n) : w (g⁻¹ * k) = ∑ i, (c i * α i g) * β i k := by
    have hh := (congrFun (congrFun hs g) k).symm
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
    simp_rw [hβ, ← mul_assoc] at hh
    exact hh
  have hEq : (fun x : K n => convolution w φ (x * g)) = ∑ i, (c i * α i g) • F i := by
    funext x
    have hi (i : Fin m) : Integrable (fun k : K n => (c i * α i g) * (β i k * φ (x * k))) νK :=
      integrable_compact (continuous_const.mul ((β i).continuous.mul (hφ.comp (continuous_const.mul continuous_id))))
    change (∫ k, w k * φ ((x * g) * k) ∂νK) = _
    have he : (∫ k : K n, w k * φ (x * g * k) ∂νK) = ∫ k, w (g⁻¹ * k) * φ (x * k) ∂νK := by
      conv_rhs => rw [← integral_mul_left_eq_self _ g]
      simp only [inv_mul_cancel_left, mul_assoc]
    have hpoint (k : K n) : w (g⁻¹ * k) * φ (x * k) =
        ∑ i, (c i * α i g) * (β i k * φ (x * k)) := by
      rw [hrep, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
    rw [he]
    simp_rw [hpoint]
    rw [integral_finsetSum]
    · simp only [integral_const_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, F, convolution]
    · exact fun i _ => hi i
  change (fun x : K n => convolution w φ (x * g)) ∈ Submodule.span ℂ (range F)
  rw [hEq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem convolution_left (w : C(K n, ℂ))
    (hcentral : ∀ g k, w (g * k * g⁻¹) = w k) (φ : K n → ℂ) (x : K n) :
    convolution w φ x = ∫ k, w k * φ (k * x) ∂νK := by
  let F (k : K n) := w k * φ (k * x)
  have hi : ∫ k, F (x * k * x⁻¹) ∂νK = ∫ k, F k ∂νK := by
    rw [integral_mul_left_eq_self (fun k => F (k * x⁻¹)) x, integral_mul_right_eq_self]
  rw [← hi]
  change _ = ∫ k, w (x * k * x⁻¹) * φ ((x * k * x⁻¹) * x) ∂νK
  simp_rw [hcentral]
  simp only [mul_assoc, inv_mul_cancel, mul_one, convolution]

private theorem continuous_compactFunctionDifference (ks : List (K n)) {φ : K n → ℂ}
    (hφ : Continuous φ) : Continuous (compactFunctionDifference ks φ) := by
  induction ks with
  | nil => exact hφ
  | cons k ks ih => exact (ih.comp (continuous_id.mul continuous_const)).sub ih

private theorem compactFunctionDifference_sub (ks : List (K n)) (φ ψ : K n → ℂ) :
    compactFunctionDifference ks (φ - ψ) = compactFunctionDifference ks φ - compactFunctionDifference ks ψ := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    funext x
    change compactFunctionDifference ks (φ - ψ) (x * k) - compactFunctionDifference ks (φ - ψ) x = _
    rw [ih]
    change (compactFunctionDifference ks φ (x * k) - compactFunctionDifference ks ψ (x * k)) -
      (compactFunctionDifference ks φ x - compactFunctionDifference ks ψ x) =
      (compactFunctionDifference ks φ (x * k) - compactFunctionDifference ks φ x) -
        (compactFunctionDifference ks ψ (x * k) - compactFunctionDifference ks ψ x)
    abel

private theorem convolution_compactFunctionDifference (w : C(K n, ℂ))
    (hcentral : ∀ g k, w (g * k * g⁻¹) = w k) (ks : List (K n)) {φ : K n → ℂ}
    (hφ : Continuous φ) :
    compactFunctionDifference ks (convolution w φ) = convolution w (compactFunctionDifference ks φ) := by
  induction ks with
  | nil => rfl
  | cons t ks ih =>
    funext x
    let ψ := compactFunctionDifference ks φ
    have hψ : Continuous ψ := continuous_compactFunctionDifference ks hφ
    have hi (y : K n) : Integrable (fun k : K n => w k * ψ (k * y)) νK :=
      integrable_compact (w.continuous.mul (hψ.comp (continuous_id.mul continuous_const)))
    change compactFunctionDifference ks (convolution w φ) (x * t) -
      compactFunctionDifference ks (convolution w φ) x = convolution w (fun y => ψ (y * t) - ψ y) x
    rw [ih, convolution_left w hcentral _ (x * t), convolution_left w hcentral _ x,
      convolution_left w hcentral _ x, ← integral_sub (hi (x * t)) (hi x)]
    simp only [mul_assoc, mul_sub]

/-- The first displacement moment controls a central convolution error at each difference order. -/
theorem convolution_error (w : C(K n, ℂ)) (W : K n → ℝ)
    (hW : Continuous W) (hPos : ∀ k, 0 ≤ W k) (hwW : ∀ k, w k = (W k : ℂ))
    (hcentral : ∀ g k, w (g * k * g⁻¹) = w k) (hMass : ∫ k, W k ∂νK = 1)
    {φ : K n → ℂ} (hφ : Continuous φ) {J : ℕ} {D ε : ℝ} (hD : 0 ≤ D)
    (h : CompactProfileDifferenceBound (J + 1) φ D)
    (hMoment : (∫ k, W k * ‖k.val - 1‖ ∂νK) ≤ ε) :
    CompactProfileDifferenceBound J (convolution w φ - φ) (D * ε) := by
  intro ks hks x
  let ψ := compactFunctionDifference ks φ
  let R := D * displacementProduct ks
  have hR : 0 ≤ R := mul_nonneg hD (displacementProduct_nonneg ks)
  have hψ : Continuous ψ := continuous_compactFunctionDifference ks hφ
  have hMass' : ∫ k, w k ∂νK = 1 := by
    simp_rw [hwW]
    rw [integral_complex_ofReal, hMass, Complex.ofReal_one]
  have hConst : ∫ k, w k * ψ x ∂νK = ψ x := by rw [integral_mul_const, hMass', one_mul]
  have hEq : convolution w ψ x - ψ x = ∫ k, w k * (ψ (x * k) - ψ x) ∂νK := by
    have hLeft : Integrable (fun k : K n => w k * ψ (x * k)) νK :=
      integrable_compact (w.continuous.mul (hψ.comp (continuous_const.mul continuous_id)))
    have hRight : Integrable (fun k : K n => w k * ψ x) νK :=
      integrable_compact (w.continuous.mul continuous_const)
    simp_rw [mul_sub]
    rw [integral_sub hLeft hRight, hConst]
    rfl
  rw [compactFunctionDifference_sub, convolution_compactFunctionDifference w hcentral ks hφ]
  change ‖convolution w ψ x - ψ x‖ ≤ (D * ε) * displacementProduct ks
  rw [hEq]
  have hI : Integrable (fun k : K n => R * (W k * ‖k.val - 1‖)) νK :=
    integrable_compact (continuous_const.mul (hW.mul (continuous_subtype_val.sub continuous_const).norm))
  have hN := norm_integral_le_of_norm_le (f := fun k : K n => w k * (ψ (x * k) - ψ x)) hI
    (Filter.Eventually.of_forall fun k => ?_)
  · rw [integral_const_mul] at hN
    exact hN.trans ((mul_le_mul_of_nonneg_left hMoment hR).trans_eq (by dsimp only [R]; ring))
  · rw [norm_mul, hwW, Complex.norm_real, Real.norm_of_nonneg (hPos k)]
    have hd := h (k :: ks) (Nat.succ_le_succ hks) x
    change ‖ψ (x * k) - ψ x‖ ≤ D * (‖k.val - 1‖ * displacementProduct ks) at hd
    calc
      _ ≤ W k * (D * (‖k.val - 1‖ * displacementProduct ks)) := mul_le_mul_of_nonneg_left hd (hPos k)
      _ = _ := by dsimp only [R]; ring

/-- Averaging any smooth standard section over the actual right compact action with a
polynomial weight produces a compact-finite standard vector. -/
theorem exists_standard_convolution (ds : List ComplexCharacterData) (F : G n → ℂ)
    (hF : F ∈ complexStandardModule n ds) (w : C(K n, ℂ)) (hw : w ∈ polynomialStar n) :
    ∃ f : Std n ds, ∀ x : G n,
      f.val x = ∫ k : K n, w k * F (x * Unitary.toUnits k) ∂compactMatrixHaar n := by
  let φ (k : K n) := F (Unitary.toUnits k)
  have hφ : Continuous φ := hF.1.continuous.comp continuous_unitary_toUnits
  have hv := continuous_convolution w hφ
  have hfinite := convolution_finite hw hφ
  have hPhase (a : Fin n → ℂˣ) (k : K n) : φ (phaseMatrix a * k) =
      principalSeriesCharacter ℂ n (complexPositionCharacter ds)
        (fun i => phaseUnit (a i)) * φ k := by
    have he : Unitary.toUnits (phaseMatrix a) =
        Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun i => phaseUnit (a i)) := by
      apply Units.ext
      change (phaseMatrix a).val = _
      rw [phaseMatrix_val]
      rfl
    change F (Unitary.toUnits (phaseMatrix a * k)) = _
    rw [map_mul, he]
    simpa only [Subgroup.coe_one, mul_one] using hF.2 (fun i => phaseUnit (a i)) 1 (Unitary.toUnits k)
  obtain ⟨f, hf, hApply⟩ := complexPrincipalSeriesExtension n ds (convolution w φ) hv hfinite (by
    intro a k
    simp only [convolution, mul_assoc, hPhase]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring))
  refine ⟨⟨f, hf⟩, fun x => ?_⟩
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary x
  let χ := principalSeriesCharacter ℂ n (complexPositionCharacter ds) a
  let k₀ : K n := ⟨k.val, hk⟩
  have hk₀ : Unitary.toUnits k₀ = k := Units.ext rfl
  have hf₀ : f k = convolution w φ k₀ := hk₀ ▸ hApply k₀
  change f ((Langlands.GeneralLinear.Iwasawa.diagonalUnits a : G n) * u.val * k) = _
  rw [hf.1.2 a u k, hf₀, convolution, ← integral_const_mul]
  apply integral_congr_ae (ae_of_all _ fun j => ?_)
  change χ * (w j * F (Unitary.toUnits (k₀ * j))) =
    w j * F ((Langlands.GeneralLinear.Iwasawa.diagonalUnits a : G n) * u.val * k * Unitary.toUnits j)
  rw [Unitary.toUnits.map_mul, hk₀, mul_assoc _ k (Unitary.toUnits j), hF.2 a u]
  exact mul_left_comm _ _ _

/-- Compact-finite standard vectors approximate every smooth standard section
in each compact difference bound for which the section has one additional order. -/
def ComplexCompactDifferenceDensityStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (F : G n → ℂ), F ∈ complexStandardModule n ds →
  ∀ (J : ℕ) (D ε : ℝ), 0 ≤ D → 0 < ε →
    CompactProfileDifferenceBound (J + 1) (fun k => F (Unitary.toUnits k)) D →
    ∃ f : Std n ds, CompactProfileDifferenceBound J
      (fun k => f.val (Unitary.toUnits k) - F (Unitary.toUnits k)) (D * ε)

set_option maxHeartbeats 750000 in
theorem complexCompactDifferenceDensity : ComplexCompactDifferenceDensityStatement := by
  intro n ds F hF J D ε hD hε h
  let φ (k : K n) := F (Unitary.toUnits k)
  have hφ : Continuous φ := hF.1.continuous.comp continuous_unitary_toUnits
  obtain ⟨w, W, hw, hW, hPos, hwW, hcentral, hMass, hMoment⟩ := complexCentralPolynomialWeight n ε hε
  obtain ⟨f, hf⟩ := exists_standard_convolution ds F hF w hw
  have hApply (k : K n) : f.val (Unitary.toUnits k) = convolution w φ k := by
    rw [hf]
    unfold convolution φ
    simp_rw [Unitary.toUnits.map_mul]
  refine ⟨f, ?_⟩
  simp_rw [hApply]
  exact convolution_error w W hW hPos hwW hcentral hMass hφ hD h hMoment.le

end Langlands.Global.RankinSelbergGlobal.ComplexCompactDifferenceDensity
