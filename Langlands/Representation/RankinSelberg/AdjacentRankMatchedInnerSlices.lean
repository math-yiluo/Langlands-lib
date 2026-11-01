import Langlands.Representation.RankinSelberg.AdjacentRankInnerSliceSeparation
import Langlands.Representation.RankinSelberg.AdjacentRankDualCompactCoefficients

/-! Matched original and transformed inner determinant-slice expansions. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matchedInnerFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance matchedInnerValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance matchedInnerLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance matchedInnerFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance matchedInnerGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance matchedInnerGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance matchedInnerGroupSecondCountable (r : ℕ) :
    SecondCountableTopology (GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (r + 1)
local instance matchedInnerGroupSigmaCompact (r : ℕ) :
    SigmaCompactSpace (GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (r + 1)

/-- The literal transformed inner determinant-slice integral. -/
def adjacentRankDualInnerSliceIntegral {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier) (j : ℤ) (s : ℂ)
    (W : GeneralLinear (r + 1) F.Carrier → ℂ)
    (g : GeneralLinear (r + 1) F.Carrier) : ℂ :=
  ∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * dualFunction r W (g * h)
    ∂generalLinearHaar F.Carrier r

private theorem integral_sum_of_normalized_average {r N : ℕ}
    (K : OpenSubgroup (GeneralLinear (r + 1) F.Carrier))
    (hKc : IsCompact (K : Set (GeneralLinear (r + 1) F.Carrier)))
    (a v : GeneralLinear (r + 1) F.Carrier → ℂ) (c : Fin N → ℂ)
    (f : Fin N → GeneralLinear (r + 1) F.Carrier → ℂ)
    (ha : ∀ k ∈ K, ∀ h, a (k * h) = a h)
    (hv : Integrable (fun h => a h * v h) (generalLinearHaar F.Carrier r))
    (hf : ∀ i, Integrable (fun h => a h * f i h) (generalLinearHaar F.Carrier r))
    (havg : ∀ h, ((generalLinearHaar F.Carrier r).real (K : Set _) : ℂ)⁻¹ *
      (∫ k in (K : Set _), v (k * h) ∂generalLinearHaar F.Carrier r) =
        ∑ i, c i * f i h) :
    (∫ h, a h * v h ∂generalLinearHaar F.Carrier r) =
      ∑ i, c i * ∫ h, a h * f i h ∂generalLinearHaar F.Carrier r := by
  let η := generalLinearHaar F.Carrier r
  let mass : ℂ := η.real (K : Set _)
  have hmass : mass ≠ 0 :=
    GodementJacquet.Padic.measureReal_openSubgroup_ne_zero F K hKc
  obtain ⟨_, hval⟩ := GodementJacquet.leftAverage_integral η (K : Set _)
    K.isOpen.measurableSet hKc.measure_lt_top.ne a v ha hv
  have hnorm :
      (∫ h, a h * (mass⁻¹ * ∫ k in (K : Set _), v (k * h) ∂η) ∂η) =
        ∫ h, a h * v h ∂η := by
    calc
      _ = mass⁻¹ * ∫ h, a h * (∫ k in (K : Set _), v (k * h) ∂η) ∂η := by
        rw [← integral_const_mul]
        congr 1
        funext h
        ring
      _ = _ := by rw [hval, ← mul_assoc, inv_mul_cancel₀ hmass, one_mul]
  calc
    _ = ∫ h, a h * (mass⁻¹ * ∫ k in (K : Set _), v (k * h) ∂η) ∂η := hnorm.symm
    _ = ∫ h, ∑ i, c i * (a h * f i h) ∂η := by
      apply integral_congr_ae
      filter_upwards [] with h
      rw [havg h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hf i).const_mul _)]
      simp only [integral_const_mul]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1600000 in
/-- A common averaging subgroup gives simultaneous original and transformed
inner slice expansions with exactly the same finite family and matrix
coefficients, for any two fixed square tests and determinant characters. -/
theorem adjacentRankInnerSlice_matchedFiniteSeparation
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsAdmissible σ) (ℓ : glFunctionals ψ r σ)
    (Φ ΦD : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ χD : Quasicharacter F.Carrier) :
    ∃ (N : ℕ) (B : Fin N → (glCoefficientModel ψ r σ ℓ).toSubmodule),
      ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ),
          ∀ (j : ℤ) (s : ℂ) (g : GeneralLinear (r + 1) F.Carrier),
            Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j s h *
              W.val.val (g * h)) (generalLinearHaar F.Carrier r) ∧
            Integrable (fun h => adjacentRankInnerSliceWeight F ΦD χD j s h *
              dualFunction r W.val.val (g * h)) (generalLinearHaar F.Carrier r) ∧
            (∀ i, Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j s h * (f i).val h)
                (generalLinearHaar F.Carrier r) ∧
              Integrable (fun h => adjacentRankInnerSliceWeight F ΦD χD j s h *
                GodementJacquet.coefficientIota (f i).val h) (generalLinearHaar F.Carrier r)) ∧
            (∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * W.val.val (g * h)
              ∂generalLinearHaar F.Carrier r) =
                ∑ i, (B i).val.val g *
                  ∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * (f i).val h
                    ∂generalLinearHaar F.Carrier r ∧
            adjacentRankDualInnerSliceIntegral F ΦD χD j s W.val.val g =
              ∑ i, (dualModelLinearMap ψ σ ℓ (B i)).val.val g *
                ∫ h, adjacentRankInnerSliceWeight F ΦD χD j s h *
                  GodementJacquet.coefficientIota (f i).val h ∂generalLinearHaar F.Carrier r := by
  obtain ⟨K₀, hK₀c, hK₀ι, hK₀⟩ := exists_adjacentRankInner_subgroup F Φ χ
  obtain ⟨K₁, _, hK₁ι, hK₁⟩ := exists_adjacentRankInner_subgroup F ΦD χD
  let K := K₀ ⊓ K₁
  have hKc : IsCompact (K : Set (GeneralLinear (r + 1) F.Carrier)) :=
    hK₀c.inter_right K₁.isClosed
  have hKι : ∀ k ∈ K, inverseTranspose (r + 1) F.Carrier k ∈ K :=
    fun k hk => ⟨hK₀ι k hk.1, hK₁ι k hk.2⟩
  obtain ⟨N, B, hB⟩ := adjacentRankCompact_middleAverage_and_dual F ψ σ hσ ℓ K hKc hKι
  refine ⟨N, B, fun W => ?_⟩
  obtain ⟨f, hfo, hfd⟩ := hB W
  refine ⟨f, fun j s g => ?_⟩
  have hWc := glModelFunction_continuous ψ r σ hσ.1 ℓ W
  have hWdc : Continuous (dualFunction r W.val.val) := by
    change Continuous (fun h => W.val.val
      (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h))
    exact hWc.comp (continuous_const.mul (continuous_inverseTranspose (r + 1) F.Carrier))
  have hWo := integrable_adjacentRankInnerSliceWeight_mul F Φ χ j s
    (fun h => W.val.val (g * h))
    (hWc.comp (continuous_const.mul continuous_id))
  have hWd := integrable_adjacentRankInnerSliceWeight_mul F ΦD χD j s
    (fun h => dualFunction r W.val.val (g * h))
    (hWdc.comp (continuous_const.mul continuous_id))
  have hfc (i : Fin N) : Continuous (f i).val :=
    (GodementJacquet.isLocallyConstant_biSmoothMatrixCoefficients _ (f i)).continuous
  have hfi (i : Fin N) := integrable_adjacentRankInnerSliceWeight_mul F Φ χ j s _ (hfc i)
  have hfdi (i : Fin N) := integrable_adjacentRankInnerSliceWeight_mul F ΦD χD j s _
    ((hfc i).comp (continuous_inverseTranspose (r + 1) F.Carrier))
  refine ⟨hWo, hWd, fun i => ⟨hfi i, hfdi i⟩, ?_, ?_⟩
  · refine integral_sum_of_normalized_average F K hKc
      (adjacentRankInnerSliceWeight F Φ χ j s) (fun h => W.val.val (g * h))
      (fun i => (B i).val.val g) (fun i => (f i).val) ?_ hWo hfi ?_
    · intro k hk h
      obtain ⟨hΦ, hχ, hdet⟩ := hK₀ k hk.1
      exact adjacentRankInnerSliceWeight_mul F Φ χ k hΦ hχ hdet j s h
    · intro h
      simpa only [mul_assoc] using hfo g h
  · refine integral_sum_of_normalized_average F K hKc
      (adjacentRankInnerSliceWeight F ΦD χD j s)
      (fun h => dualFunction r W.val.val (g * h))
      (fun i => (dualModelLinearMap ψ σ ℓ (B i)).val.val g)
      (fun i => GodementJacquet.coefficientIota (f i).val) ?_ hWd hfdi ?_
    · intro k hk h
      obtain ⟨hΦ, hχ, hdet⟩ := hK₁ k hk.2
      exact adjacentRankInnerSliceWeight_mul F ΦD χD k hΦ hχ hdet j s h
    · intro h
      simpa only [adjacentRankDualMiddleAverage, mul_assoc] using hfd g h

end Langlands.RankinSelberg.Padic
