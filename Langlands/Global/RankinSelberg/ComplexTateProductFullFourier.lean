import Langlands.Global.RankinSelberg.ComplexTateCoordinateReflection
import Langlands.Global.RankinSelberg.ComplexTraceFourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # Common-strip reflection for the full diagonal complex Fourier transform -/

noncomputable section

open Complex MeasureTheory
open scoped ENNReal SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

open ArchimedeanLocal Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.HarmonicAnalysis (UnitaryAdditiveCharacter)
open Langlands.LocalFactor.ComplexTate (traceChar)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private abbrev positiveCharacter : UnitaryAdditiveCharacter ℂ := complexScaledCharacter 1

private theorem positiveCharacter_apply (z : ℂ) : positiveCharacter.complex z = traceChar z := by
  rw [UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply, Units.val_one,
    one_mul, Algebra.trace_complex_apply, Real.fourierChar_apply, traceChar]
  congr 1
  push_cast
  ring

private theorem selfDual_measure_neg_one :
    (complexSelfDualMeasure (-1 : ℂˣ)).measure = ComplexTate.measure := by
  rw [ComplexTraceFourier.measure_eq, ComplexTraceFourier.scale, ComplexTate.measure,
    ← Measure.coe_nnreal_smul]
  simp

private def decay (z : ℂ) : ℝ := ((max 1 ‖z‖) ^ 3)⁻¹

private theorem integrable_decay : Integrable decay ComplexTate.measure := by
  have h₃ : (Module.finrank ℝ ℂ : ℝ) < (3 : ℝ) := by norm_num [Complex.finrank_real_complex]
  have h : Integrable (fun z : ℂ => (1 + ‖z‖) ^ (-(3 : ℝ))) (volume : Measure ℂ) :=
    integrable_one_add_norm h₃
  have hd : Integrable decay (volume : Measure ℂ) := by
    refine (h.const_mul 8).mono' (by unfold decay; fun_prop) (ae_of_all _ fun z => ?_)
    rw [decay, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.rpow_neg (by positivity), Real.rpow_ofNat]
    have hle : 1 + ‖z‖ ≤ 2 * max 1 ‖z‖ := by
      linarith [le_max_left (1 : ℝ) ‖z‖, le_max_right (1 : ℝ) ‖z‖]
    have hpow : (1 + ‖z‖) ^ 3 ≤ 8 * (max 1 ‖z‖) ^ 3 := by
      calc
        _ ≤ (2 * max 1 ‖z‖) ^ 3 := pow_le_pow_left₀ (by positivity) hle _
        _ = _ := by rw [mul_pow]; norm_num
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity),
      one_mul]
    exact hpow
  exact hd.smul_measure (by simp)

variable {n : ℕ}
local notation "V" => Fin (n + 1) → ℂ
local notation "Row" => Fin n → ℂ

private def coordinateMeasure (S : Finset (Fin (n + 1))) (x : V) (j : Fin (n + 1)) : Measure ℂ :=
  if j ∈ S then ComplexTate.measure else Measure.dirac (x j)

local instance mixedCoordinateSigmaFinite (S : Finset (Fin (n + 1))) (x : V) (j : Fin (n + 1)) :
    SigmaFinite (coordinateMeasure S x j) := by
  unfold coordinateMeasure
  split_ifs
  · rw [← selfDual_measure_neg_one]
    let := (complexSelfDualMeasure (-1 : ℂˣ)).isAddHaar
    infer_instance
  · infer_instance

private def partialKernel (S : Finset (Fin (n + 1))) (F : 𝓢(V, ℂ)) (x y : V) : ℂ :=
  F y * ∏ j ∈ S, positiveCharacter.complex (y j * x j)

private theorem partialKernel_integrable (S : Finset (Fin (n + 1))) (F : 𝓢(V, ℂ)) (x : V) :
    Integrable (partialKernel S F x) (Measure.pi (coordinateMeasure S x)) := by
  obtain ⟨C, _, hC⟩ := exists_norm_le_prod_decay F 3
  have hI : ∀ j, Integrable decay (coordinateMeasure S x j) := by
    intro j
    rw [coordinateMeasure]
    split_ifs
    · exact integrable_decay
    · exact integrable_dirac (by simp)
  refine ((Integrable.fintype_prod hI).const_mul C).mono' ?_
    (ae_of_all _ fun y => ?_)
  · refine (F.continuous.mul (continuous_finsetProd S fun j _ => ?_)).aestronglyMeasurable
    exact positiveCharacter.continuous_complex.comp ((continuous_apply j).mul continuous_const)
  · simpa only [partialKernel, norm_mul, norm_prod, UnitaryAdditiveCharacter.norm_complex,
      Finset.prod_const_one, mul_one, decay] using hC y

private theorem integral_split (μ : Fin (n + 1) → Measure ℂ) [∀ j, SigmaFinite (μ j)]
    (i : Fin (n + 1)) (K : V → ℂ) (hK : Integrable K (Measure.pi μ)) :
    (∫ y, K y ∂Measure.pi μ) =
      ∫ z, (∫ w : Row, K (i.insertNth z w) ∂Measure.pi (fun j => μ (i.succAbove j))) ∂μ i := by
  let e : ℂ × Row ≃ᵐ V := (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) i).symm
  have he := (measurePreserving_piFinSuccAbove μ i).symm e.symm
  have hI : Integrable (fun p : ℂ × Row => K (e p))
      ((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr hK
  rw [← he.integral_comp' (f := e) K, integral_prod _ hI]
  rfl

private theorem pi_dirac (x : V) :
    (Measure.pi fun j => Measure.dirac (x j)) = Measure.dirac x := by
  refine Measure.pi_eq fun s hs => ?_
  by_cases hx : ∀ i, x i ∈ s i
  · rw [Measure.dirac_apply_of_mem (Set.mem_pi.mpr (fun j _ => hx j))]
    simp only [Measure.dirac_apply_of_mem (hx _), Finset.prod_const_one]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    rw [Measure.dirac_apply, Set.indicator_of_notMem
      (fun h => hi (Set.mem_pi.mp h i (Set.mem_univ i)))]
    exact (Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [Measure.dirac_apply, Set.indicator_of_notMem hi])).symm

private theorem coordinateFourier_formula (G : 𝓢(V, ℂ)) (i : Fin (n + 1)) (x : V) :
    coordinateFourier G i x =
      ∫ z, positiveCharacter.complex (z * x i) * G (Function.update x i z) ∂ComplexTate.measure := by
  conv_lhs => rw [← Fin.insertNth_self_removeNth i x]
  rw [coordinateFourier_insertNth, Langlands.LocalFactor.ComplexTate.fourier_apply]
  simp only [coordinateSlice_apply, Fin.insertNth_removeNth, positiveCharacter_apply]

private theorem partial_insert (F G : 𝓢(V, ℂ)) {S : Finset (Fin (n + 1))} {i : Fin (n + 1)}
    (hi : i ∉ S)
    (hG : ∀ x, G x = ∫ y, partialKernel S F x y ∂Measure.pi (coordinateMeasure S x))
    (x : V) :
    coordinateFourier G i x =
      ∫ y, partialKernel (insert i S) F x y ∂Measure.pi (coordinateMeasure (insert i S) x) := by
  let R : Measure Row := Measure.pi fun j => coordinateMeasure S x (i.succAbove j)
  have hnew : (Measure.pi fun j : Fin n => coordinateMeasure (insert i S) x (i.succAbove j)) = R := by
    simp [R, coordinateMeasure, i.succAbove_ne]
  have hold (z : ℂ) :
      (Measure.pi fun j : Fin n => coordinateMeasure S (Function.update x i z) (i.succAbove j)) = R := by
    simp [R, coordinateMeasure, i.succAbove_ne]
  rw [coordinateFourier_formula, integral_split _ i _ (partialKernel_integrable (insert i S) F x),
    hnew, show coordinateMeasure (insert i S) x i = ComplexTate.measure by simp [coordinateMeasure]]
  apply integral_congr_ae
  filter_upwards with z
  rw [hG, integral_split _ i _ (partialKernel_integrable S F (Function.update x i z)),
    hold, show coordinateMeasure S (Function.update x i z) i = Measure.dirac z by
      simp [coordinateMeasure, hi], integral_dirac, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  let y : V := i.insertNth z w
  change _ * partialKernel S F (Function.update x i z) y = partialKernel (insert i S) F x y
  have hy : y i = z := by simp [y]
  simp only [partialKernel, Finset.prod_insert hi, hy]
  have he : (∏ j ∈ S, positiveCharacter.complex
      (y j * Function.update x i z j)) =
      ∏ j ∈ S, positiveCharacter.complex (y j * x j) :=
    Finset.prod_congr rfl (fun j hj => by
      rw [Function.update_of_ne (show j ≠ i from fun h => hi (h ▸ hj))])
  rw [he]
  ring

private def weightOn (S : Finset (Fin (n + 1))) (m : Fin (n + 1) → ℤ) (j : Fin (n + 1)) : ℤ :=
  if j ∈ S then -m j else m j

private def parameterOn (S : Finset (Fin (n + 1))) (u : V) (j : Fin (n + 1)) : ℂ :=
  if j ∈ S then 1 - u j else u j

private theorem exists_partial (F : 𝓢(V, ℂ)) (m : Fin (n + 1) → ℤ) (u : V)
    (hu : ∀ j, 0 < (u j).re) (hu' : ∀ j, (u j).re < 1) (S : Finset (Fin (n + 1))) :
    ∃ G : 𝓢(V, ℂ),
      (∀ x, G x = ∫ y, partialKernel S F x y ∂Measure.pi (coordinateMeasure S x)) ∧
      normalizedZeta G (weightOn S m) (parameterOn S u) =
        (∏ j ∈ S, I ^ (m j).natAbs) * normalizedZeta F m u := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨F, fun x => ?_, ?_⟩
    · rw [show coordinateMeasure ∅ x = (fun j => Measure.dirac (x j)) from
          funext fun j => by simp [coordinateMeasure], pi_dirac]
      simp [partialKernel, integral_dirac]
    · rw [show weightOn ∅ m = m from funext fun j => by simp [weightOn],
        show parameterOn ∅ u = u from funext fun j => by simp [parameterOn]]
      simp
  | @insert i S hi ih =>
    obtain ⟨G, hG, hN⟩ := ih
    refine ⟨coordinateFourier G i, partial_insert F G hi hG, ?_⟩
    have hp (j : Fin (n + 1)) : 0 < (parameterOn S u j).re := by
      by_cases hj : j ∈ S
      · simpa [parameterOn, hj] using sub_pos.mpr (hu' j)
      · simpa [parameterOn, hj] using hu j
    have hp' : (parameterOn S u i).re < 1 := by simpa [parameterOn, hi] using hu' i
    have hW : reflectedWeight i (weightOn S m) = weightOn (insert i S) m := by
      funext j
      by_cases hj : j = i <;> simp [reflectedWeight, weightOn, hj, hi]
    have hP : reflectedParameter i (parameterOn S u) = parameterOn (insert i S) u := by
      funext j
      by_cases hj : j = i <;> simp [reflectedParameter, parameterOn, hj, hi]
    have e := normalizedZeta_coordinateFourier G i (weightOn S m) (parameterOn S u) hp hp'
    rw [hW, hP, weightOn, ite_eq_right hi, hN] at e
    rw [Finset.prod_insert hi, mul_assoc]
    exact e

private theorem partialKernel_univ (F : 𝓢(V, ℂ)) (x y : V) :
    partialKernel Finset.univ F x y =
      F y * (complexScaledCharacter (-1 : ℂˣ)).complex (-∑ j, y j * x j) := by
  have hchar (z : ℂ) : (complexScaledCharacter (-1 : ℂˣ)).complex (-z) =
      positiveCharacter.complex z := by
    simp [UnitaryAdditiveCharacter.complex_apply]
  rw [partialKernel, hchar]
  congr 1
  have hsum (S : Finset (Fin (n + 1))) :
      positiveCharacter.complex (∑ j ∈ S, y j * x j) =
        ∏ j ∈ S, positiveCharacter.complex (y j * x j) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]
  exact (hsum Finset.univ).symm

/-- The full positive trace Fourier transform reflects every coordinate of the normalized
product Tate integral on the common strip. -/
def ComplexTateProductFullFourierStatement : Prop :=
  ∀ (n : ℕ) (F : 𝓢(Fin (n + 1) → ℂ, ℂ)) (m : Fin (n + 1) → ℤ) (u : Fin (n + 1) → ℂ),
    (∀ j, 0 < (u j).re) → (∀ j, (u j).re < 1) →
      normalizedZeta (ComplexTraceFourier.transform (-1) F) (fun j => -m j) (fun j => 1 - u j) =
        (∏ j, I ^ (m j).natAbs) * normalizedZeta F m u

theorem complexTateProductFullFourier : ComplexTateProductFullFourierStatement := by
  intro n F m u hu hu'
  obtain ⟨G, hG, hN⟩ := exists_partial F m u hu hu' Finset.univ
  have hEq : G = ComplexTraceFourier.transform (-1) F := by
    ext x
    rw [hG, ComplexTraceFourier.transform_apply (-1) F x]
    rw [show coordinateMeasure Finset.univ x = (fun _ => ComplexTate.measure) from
      funext fun j => by simp [coordinateMeasure]]
    simp only [selfDual_measure_neg_one, partialKernel_univ]
  rwa [hEq, show weightOn Finset.univ m = (fun j => -m j) from funext fun j => by simp [weightOn],
    show parameterOn Finset.univ u = (fun j => 1 - u j) from
      funext fun j => by simp [parameterOn]] at hN

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
