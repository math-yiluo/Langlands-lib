import Langlands.Global.RankinSelberg.ArchimedeanRealPairIdentity
import Langlands.Global.RankinSelberg.RealRectangularIntegralTransfer
import Langlands.Global.RankinSelberg.RealRectangularRows
import Langlands.Global.RankinSelberg.RealSmoothRowCharacterAbsorption
import Langlands.Representation.Archimedean.SmoothVectorSubgroupFactorization

/-! # Smooth vector factorization along real rectangular rows -/

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealRectangularRows

open ArchimedeanLocal Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)
open RealUnequalLastRowDescent (colUnip)
open RealSmoothRowCharacterAbsorption (realSmoothRowCharacterAbsorptionAllEvaluations)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "Mat" => fun n : ℕ => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
local notation "Q" => fun t : ℕ => LeftUnipotentQuotient t ℝ
local notation "Row" => fun t : ℕ => Fin (t + 1) → ℝ
local notation "X" => fun j t : ℕ => Matrix (Fin j) (Fin (t + 1)) ℝ
local notation "expU" => Langlands.LinearLieGroup.expUnit

variable {A E : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors I R
local notation "act" => DerivativeSmoothVectors.representation I R

variable {r t : ℕ} (h : t < r) (ρ : G r →* Aˣ)

/-- A coefficient obtained by inserting the leading rectangular variable into the given action. -/
def prefixKernel (L : Q t → D →L[ℂ] ℂ) (wt : ℂ → Q t → ℂ)
    (j : ℕ) (v : D) (s : ℂ) (p : Q t × X j t) : ℂ :=
  L p.1 (act (ρ (point h p.1.out p.2)) v) * wt s p.1

private theorem exists_rowMeasure_smul_volume (ν : AdditiveHaarMeasure ℝ) (m : ℕ) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ rowMeasure ν m = c • (volume : Measure (Fin m → ℝ)) := by
  let μ := rowMeasure ν m
  have : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  have : SigmaFinite ν.measure := inferInstance
  have : μ.IsAddHaarMeasure := rowMeasure_isAddHaar ν m
  let c := Measure.addHaarScalarFactor μ volume
  have hc : μ = c • (volume : Measure (Fin m → ℝ)) := Measure.isAddLeftInvariant_eq_smul μ volume
  refine ⟨c, ?_, hc⟩
  intro he
  have hm : μ ≠ 0 := Measure.measure_univ_pos.mp (isOpen_univ.measure_pos μ Set.univ_nonempty)
  apply hm
  rw [hc, he, zero_smul]

private theorem row_step (hR : IsContinuousRepresentation R) (hρ : Continuous ρ)
    (a : ℝˣ) (ν : AdditiveHaarMeasure ℝ) (j : ℕ) (hj : j < r - (t + 1))
    (F : Row t →ₗ[ℝ] A) (hComm : ∀ y z, Commute (F y) (F z))
    (hExp : ∀ y, expU A (F y) = ρ (expU (Mat r) (rowDirections r t j y)))
    (L : Q t → D →L[ℂ] ℂ) (wt : ℂ → Q t → ℂ)
    (hCov : ∀ (q : Q t) (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) (v : D),
      L q (act (ρ u.val) v) = realWhittakerCharacter a u.val * L q v)
    (hH : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Row t, Langlands.Archimedean.unitHeight (ρ (colUnip (extendColumn (j + 1) y))) ≤ K * max 1 ‖y‖)
    (hN : ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ y : Row t,
      ‖R (ρ (colUnip (extendColumn (j + 1) y)))‖ ≤ C * Langlands.Archimedean.unitHeight (ρ (colUnip (extendColumn (j + 1) y))) ^ d)
    (v : D) : ∃ (n : ℕ) (u : Fin n → D), ∀ (s : ℂ) (p : Q t × X j t),
      prefixKernel R h ρ L wt j v s p =
        ∑ i, ∫ y, prefixKernel R h ρ L wt (j + 1) (u i) s (p.1, Fin.lastCases y p.2)
          ∂(rowMeasure ν (t + 1)) := by
  let col (y : Row t) := ρ (colUnip (r := r) (extendColumn (j + 1) y))
  have hCol : Continuous col := by
    apply hρ.comp
    apply (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) (r + 1)).isInducing.continuous_iff.mpr
    change Continuous (fun y : Row t => (1 : Mat r) + RealUnequalLastRowDescent.colEntries (extendColumn (j + 1) y))
    exact continuous_const.add (continuous_matrix fun i l => by
      unfold RealUnequalLastRowDescent.colEntries extendColumn
      split_ifs <;> first | exact continuous_const | exact continuous_apply _)
  obtain ⟨n, w, Φ₀, hΦ₀, hF⟩ := smoothVectorCommutingDirectionsFactorization A E R hR (t + 1) F hComm v
  obtain ⟨c, hc, hMeasure⟩ := exists_rowMeasure_smul_volume ν (t + 1)
  let Φ (i : Fin n) : 𝓢(Row t, ℂ) := ((c : ℂ)⁻¹) • (hΦ₀ i).2.toSchwartzMap (hΦ₀ i).1
  have hc₀ : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by exact_mod_cast hc)
  let P (p : Q t × X (j + 1) t) := ρ (point h p.1.out p.2)
  let row (p : Q t × X (j + 1) t) := p.2 (Fin.last j)
  have hApply (i : Fin n) : ∃ u : D, ∀ (q : Q t) (x : X (j + 1) t),
      L q (act (ρ (point h q.out x)) u) = L q (act (ρ (point h q.out x)) (w i)) * Φ i (x (Fin.last j)) := by
    -- The averaged vector is independent of the evaluation form and of the point.
    obtain ⟨u, hu⟩ := realSmoothRowCharacterAbsorptionAllEvaluations R hR (t + 1) a col hCol hH hN
      (Q t × X (j + 1) t) (fun p => L p.1) P row (by
        rintro ⟨q, x⟩ y z
        obtain ⟨u, hu, hχ⟩ := realRectangularRowAction r t j h hj a q.out x y
        change L q (act (ρ (point h q.out x)) (act (ρ (colUnip (extendColumn (j + 1) y))) z)) = _
        rw [← Module.End.mul_apply, ← map_mul, ← map_mul, hu, map_mul, map_mul,
          Module.End.mul_apply, hCov, hχ]) (w i) (Φ i)
    exact ⟨u, fun q x => hu (q, x)⟩
  choose u hu using hApply
  refine ⟨n, u, fun s p => ?_⟩
  let q := p.1
  let x := p.2
  let Lq := L q
  let Lx := Lq.comp (SmoothAction.derivativeAction I R (ρ (point h q.out x)))
  have hValue (i : Fin n) (y : Row t) : prefixKernel R h ρ L wt (j + 1) (u i) s
      (q, Fin.lastCases y x) = (c : ℂ)⁻¹ * (Φ₀ i y * Lx (act (expU A (F y)) (w i))) * wt s q := by
    unfold prefixKernel
    change Lq (act (ρ (point h q.out (Fin.lastCases y x))) (u i)) * wt s q = _
    rw [hu i, Fin.lastCases_last, point_append h hj, map_mul, map_mul, Module.End.mul_apply, hExp]
    change Lx (act (ρ (expU (Mat r) (rowDirections r t j y))) (w i)) * Φ i y * wt s q = _
    simp only [Φ, _root_.smul_apply, smul_eq_mul, HasCompactSupport.toSchwartzMap_toFun]
    ring
  change Lx v * wt s q = ∑ i, ∫ y, prefixKernel R h ρ L wt (j + 1) (u i) s
    (q, Fin.lastCases y x) ∂(rowMeasure ν (t + 1))
  rw [hF Lx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [hValue i]
  rw [hMeasure, integral_smul_nnreal_measure, integral_mul_const, integral_const_mul,
    NNReal.smul_def, Complex.real_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc₀, one_mul]

/-- A rectangular prefix is a finite sum of terminal rectangular integrals when the larger
slot acts through the supplied map. The lower row directions must lift to commuting
exponentials, and the upper columns must have moderate growth. -/
def RealRectangularSmoothTransferStatement : Prop :=
  IsContinuousRepresentation R → Continuous ρ →
  ∀ (a : ℝˣ) (μ : RealQuotientMeasureData t) (ν : AdditiveHaarMeasure ℝ)
    (L : Q t → D →L[ℂ] ℂ) (wt : ℂ → Q t → ℂ),
    (∀ (q : Q t) (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) (v : D),
      L q (act (ρ u.val) v) = realWhittakerCharacter a u.val * L q v) →
    (∀ j < r - (t + 1), ∃ F : Row t →ₗ[ℝ] A,
      (∀ y z, Commute (F y) (F z)) ∧ ∀ y, expU A (F y) = ρ (expU (Mat r) (rowDirections r t j y))) →
    (∀ j < r - (t + 1), ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Row t,
      Langlands.Archimedean.unitHeight (ρ (colUnip (extendColumn (j + 1) y))) ≤ K * max 1 ‖y‖) →
    (∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ g : Aˣ, ‖R g‖ ≤ C * Langlands.Archimedean.unitHeight g ^ d) →
    ∀ j ≤ r - (t + 1), ∀ v : D, ∃ (n : ℕ) (u : Fin n → D), ∀ s : ℂ,
      let k := r - (t + 1)
      let K := prefixKernel R h ρ L wt
      let m := fun d => μ.measure.prod (rectangularMeasure ν d (t + 1))
      (∀ i, Integrable (K k (u i) s) (m k)) → Integrable (K j v s) (m j) ∧
        (∫ p, K j v s p ∂(m j)) = ∑ i, ∫ p, K k (u i) s p ∂(m k)

set_option maxHeartbeats 950000 in
theorem realRectangularSmoothTransfer : RealRectangularSmoothTransferStatement R h ρ := by
  intro hR hρ a μ ν L wt hCov hExp hCol hNorm
  have : SigmaFinite μ.measure := ArchimedeanRealPairIdentity.sigmaFinite_measure μ
  have : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  have : SigmaFinite ν.measure := inferInstance
  apply realRectangularIntegralTransfer t μ.measure ν (r - (t + 1)) (prefixKernel R h ρ L wt)
  intro j hj v
  obtain ⟨F, hComm, hF⟩ := hExp j hj
  obtain ⟨C, d, hC, hN⟩ := hNorm
  exact row_step R h ρ hR hρ a ν j hj F hComm hF L wt hCov (hCol j hj) ⟨C, d, hC, fun y => hN _⟩ v

end Langlands.Global.RankinSelbergGlobal.RealRectangularRows
