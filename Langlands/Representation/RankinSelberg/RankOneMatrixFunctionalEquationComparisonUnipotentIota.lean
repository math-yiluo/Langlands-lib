import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentFourier
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Induction.InverseTranspose

/-! Inverse-transpose and right-translate forms of the unipotent Fourier identity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators NNReal Pointwise

namespace Langlands.RankinSelberg

universe uG uK

private theorem normalizedHaar_eq
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ η : Measure G) [μ.IsHaarMeasure] [μ.Regular] [η.IsMulLeftInvariant]
    [η.Regular]
    (J : Set G) (hμ : μ J = 1) (hη : η J = 1) : η = μ := by
  have he := Measure.isMulLeftInvariant_eq_smul_of_regular η μ
  have hc : Measure.haarScalarFactor η μ = 1 := by
    apply ENNReal.coe_injective
    have hv := congrArg (fun m : Measure G => m J) he
    simpa only [hη, Measure.smul_apply, hμ, ENNReal.smul_def, smul_eq_mul,
      mul_one, ENNReal.coe_one] using hv.symm
  rw [he, hc, one_smul]

private theorem normalizedCompactOpenHaar_inv
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (J : OpenSubgroup G) (hJ : IsCompact (J : Set G))
    [Measure.IsMulRightInvariant (normalizedCompactOpenHaar J hJ)] :
    Measure.IsInvInvariant (normalizedCompactOpenHaar J hJ) := by
  constructor
  apply normalizedHaar_eq _ _ (J : Set G) (normalizedCompactOpenHaar_self J hJ)
  rw [Measure.inv_apply]
  simpa only [inv_coe_set] using normalizedCompactOpenHaar_self J hJ

/-- Inversion preserves the actual integral-normalized unipotent Haar measure. -/
instance unipotentHaar_isInvInvariant
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ)
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) K)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) K)] :
    Measure.IsInvInvariant (unipotentHaar K n) := by
  have := localField_t2 K
  have : LocallyCompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin (n + 1) → Fin (n + 1) → K))
  have : LocallyCompactSpace (GeneralLinear.upperUnipotent (n + 1) K) :=
    GeneralLinear.UpperUnipotent.locallyCompactSpace
  have : Measure.IsMulRightInvariant
      (normalizedCompactOpenHaar (unipotentIntegralOpen K n)
        (unipotentIntegralOpen_isCompact K n)) :=
    unipotentHaar_isMulRightInvariant K n
  exact normalizedCompactOpenHaar_inv (unipotentIntegralOpen K n)
    (unipotentIntegralOpen_isCompact K n)

end Langlands.RankinSelberg

namespace Langlands.HarmonicAnalysis

open GeneralLinear

universe uK

variable {K : Type uK} [Field K]

/-- The adjacent-entry sum changes sign under inversion of an actual unipotent. -/
@[simp] theorem unipotentFourierSum_inv (n : ℕ) (u : upperUnipotent (n + 1) K) :
    unipotentFourierSum n u⁻¹ = -unipotentFourierSum n u := by
  simp only [unipotentFourierSum, UpperUnipotent.inv_adjacent_entry,
    Finset.sum_neg_distrib]

variable [TopologicalSpace K]

/-- The common inverse Whittaker phase on the two unipotent affine slices. -/
def inverseUnipotentFourierPhase (ψ : UnitaryAdditiveCharacter K)
    (n : ℕ) (u : upperUnipotent (n + 1) K) : ℂ :=
  ψ.complex (-unipotentFourierSum n u)

@[simp] theorem inverseUnipotentFourierPhase_apply (ψ : UnitaryAdditiveCharacter K)
    (n : ℕ) (u : upperUnipotent (n + 1) K) :
    inverseUnipotentFourierPhase ψ n u = ψ.complex (-unipotentFourierSum n u) := rfl

/-- The negative adjacent-entry phase is the actual inverse Whittaker character. -/
theorem unipotentFourierSum_inverseCharacter (ψ : UnitaryAdditiveCharacter K)
    (n : ℕ) (u : upperUnipotent (n + 1) K) :
    inverseUnipotentFourierPhase ψ n u =
      (Whittaker.inverseStandardCharacter ψ n u : ℂ) := by
  simp only [inverseUnipotentFourierPhase, Whittaker.inverseStandardCharacter_apply, unipotentFourierSum,
    UnitaryAdditiveCharacter.complex, AddChar.map_neg_eq_inv]

variable [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K]
variable {n : ℕ} [MeasurableSpace (upperUnipotent (n + 1) K)]
  [BorelSpace (upperUnipotent (n + 1) K)]

/-- Substitute the group inverse on the Fourier side only. The two sides now
carry the same inverse Whittaker phase; the left matrix uses inverse transpose.
Both full product integrands remain absolutely integrable. -/
theorem unipotentHaar_iota_fourier_duality (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] (hsd : IsSelfDual ψ ν)
    (μ : Measure (upperUnipotent (n + 1) K)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) K)) :
    Integrable (fun z : upperUnipotent (n + 1) K × K =>
      inverseUnipotentFourierPhase ψ n z.1 * rectangularFourierIntegral ψ ν Φ
        ((z.1⁻¹).val.val.transpose * cyclicShiftMatrix n z.2)) (μ.prod ν.measure) ∧
    Integrable (fun z : upperUnipotent (n + 1) K × (Fin n → K) =>
      inverseUnipotentFourierPhase ψ n z.1 *
        Φ (z.1.val.val * firstColumnMatrix n z.2)) (μ.prod (rowMeasure ν n)) ∧
    (∫ z : upperUnipotent (n + 1) K × K,
      inverseUnipotentFourierPhase ψ n z.1 * rectangularFourierIntegral ψ ν Φ
        ((z.1⁻¹).val.val.transpose * cyclicShiftMatrix n z.2) ∂μ.prod ν.measure) =
    ∫ z : upperUnipotent (n + 1) K × (Fin n → K),
      inverseUnipotentFourierPhase ψ n z.1 *
        Φ (z.1.val.val * firstColumnMatrix n z.2) ∂μ.prod (rowMeasure ν n) := by
  obtain ⟨hl, hu, he⟩ := unipotentHaar_transpose_fourier_duality ψ ν hsd μ Φ
  let e := upperEntryCoordinates (n + 1) (K := K)
  let : LocallyCompactSpace (upperUnipotent (n + 1) K) :=
    e.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology (upperUnipotent (n + 1) K) := e.secondCountableTopology
  let q := (Homeomorph.inv (upperUnipotent (n + 1) K)).toMeasurableEquiv.prodCongr
    (MeasurableEquiv.refl K)
  have hp : MeasurePreserving q (μ.prod ν.measure) (μ.prod ν.measure) :=
    (Measure.measurePreserving_inv μ).prod (MeasurePreserving.id ν.measure)
  have hi := hp.integrable_comp_of_integrable hl
  have heq := hp.integral_comp q.measurableEmbedding
    (fun z : upperUnipotent (n + 1) K × K =>
      ψ.complex (unipotentFourierSum n z.1) * rectangularFourierIntegral ψ ν Φ
        (z.1.val.val.transpose * cyclicShiftMatrix n z.2))
  change Integrable (fun z : upperUnipotent (n + 1) K × K =>
    ψ.complex (unipotentFourierSum n z.1⁻¹) * rectangularFourierIntegral ψ ν Φ
      ((z.1⁻¹).val.val.transpose * cyclicShiftMatrix n z.2)) _ at hi
  change (∫ z : upperUnipotent (n + 1) K × K,
    ψ.complex (unipotentFourierSum n z.1⁻¹) * rectangularFourierIntegral ψ ν Φ
      ((z.1⁻¹).val.val.transpose * cyclicShiftMatrix n z.2) ∂μ.prod ν.measure) = _ at heq
  simp only [unipotentFourierSum_inv] at hi heq
  exact ⟨hi, hu, heq.trans he⟩

end Langlands.HarmonicAnalysis

namespace Langlands.HarmonicAnalysis

open GeneralLinear

universe uK

/-- The inverse-transpose identity with a determinant-norm-one right factor:
the Fourier side carries `h`, and the original side carries `h^iota`. The
supplied scalar Haar and the actual unipotent Haar are retained. -/
theorem padicUnipotentHaar_iota_fourier_duality_right
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uK} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    haveI : BorelSpace F.Carrier := ⟨rfl⟩
    haveI : T2Space F.Carrier := RankinSelberg.localField_t2 F.Carrier
    haveI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ [MeasurableSpace (upperUnipotent (n + 1) F.Carrier)]
      [BorelSpace (upperUnipotent (n + 1) F.Carrier)]
      (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
      [SigmaFinite ν.measure], IsSelfDual ψ ν →
      ∀ (μ : Measure (upperUnipotent (n + 1) F.Carrier))
        [μ.IsHaarMeasure] [μ.IsInvInvariant]
        (h : GeneralLinear (n + 1) F.Carrier), T.determinantNorm (n + 1) h = 1 →
        ∀ Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier),
    Integrable (fun z : upperUnipotent (n + 1) F.Carrier × F.Carrier =>
      inverseUnipotentFourierPhase ψ n z.1 * rectangularFourierIntegral ψ ν Φ
        ((z.1⁻¹).val.val.transpose * cyclicShiftMatrix n z.2 * h.val))
      (μ.prod ν.measure) ∧
    Integrable (fun z : upperUnipotent (n + 1) F.Carrier × (Fin n → F.Carrier) =>
      inverseUnipotentFourierPhase ψ n z.1 *
        Φ (z.1.val.val * firstColumnMatrix n z.2 *
          (inverseTranspose (n + 1) F.Carrier h).val))
      (μ.prod (rowMeasure ν n)) ∧
    (∫ z : upperUnipotent (n + 1) F.Carrier × F.Carrier,
      inverseUnipotentFourierPhase ψ n z.1 * rectangularFourierIntegral ψ ν Φ
        ((z.1⁻¹).val.val.transpose * cyclicShiftMatrix n z.2 * h.val)
      ∂μ.prod ν.measure) =
    ∫ z : upperUnipotent (n + 1) F.Carrier × (Fin n → F.Carrier),
      inverseUnipotentFourierPhase ψ n z.1 *
        Φ (z.1.val.val * firstColumnMatrix n z.2 *
          (inverseTranspose (n + 1) F.Carrier h).val)
      ∂μ.prod (rowMeasure ν n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have : T2Space F.Carrier := RankinSelberg.localField_t2 F.Carrier
  have : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro _ _ ψ ν _ hsd μ _ _ h hh Φ
  let hi := inverseTranspose (n + 1) F.Carrier h
  have hhi : T.determinantNorm (n + 1) hi = 1 := by
    rw [T.determinantNorm_inverseTranspose, hh, inv_one]
  let Φh := rectangularLeftRightTranslate 1 hi Φ
  have hf (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
      rectangularFourierIntegral ψ ν Φh Y =
        rectangularFourierIntegral ψ ν Φ (Y * h.val) := by
    change rectangularFourierIntegral ψ ν (fun Y => Φ (1 * Y * hi.val)) Y = _
    simpa only [map_one, Units.val_one, Matrix.one_mul, hi,
      inverseTranspose_involutive] using
      padicRectangularFourierIntegral_leftRight F T (n + 1) (n + 1)
        ψ ν 1 hi (map_one _) hhi Φ Y
  have hb := unipotentHaar_iota_fourier_duality ψ ν hsd μ Φh
  simpa only [hf, Φh, rectangularLeftRightTranslate_apply, Units.val_one,
    Matrix.one_mul, hi] using hb

end Langlands.HarmonicAnalysis
