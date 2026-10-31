import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonLowerParameters
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUpperParameters

/-! The actual unipotent-coordinate Fourier identity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators NNReal

namespace Langlands.HarmonicAnalysis

open GeneralLinear

universe uK

variable {K : Type uK} [Field K]

/-- The sum of the adjacent upper entries of an actual upper-unipotent matrix. -/
def unipotentFourierSum (n : ℕ) (u : upperUnipotent (n + 1) K) : K :=
  ∑ i : Fin n, u.val.val i.castSucc i.succ

variable [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [SecondCountableTopology K] [LocallyCompactSpace K] [T2Space K]

omit [BorelSpace K] [SecondCountableTopology K] [LocallyCompactSpace K] [T2Space K] in
private theorem lower_phase (n : ℕ) (u : upperUnipotent (n + 1) K) (a : K) :
    -(∑ i : Fin n, (u.val.val.transpose * cyclicShiftMatrix n a) i.succ i.succ) =
      unipotentFourierSum n u := by
  have he (i : Fin n) :
      (u.val.val.transpose * cyclicShiftMatrix n a) i.succ i.succ =
        -u.val.val i.castSucc i.succ := by
    rw [← shiftedLowerParam_eq_transpose_mul]
    have hp := shiftedLowerParam_upperEntry n (upperEntryCoordinates (n + 1) u, a)
      ⟨(i.castSucc, i.succ), i.castSucc_lt_succ⟩
    have hc : shiftedUpperEntryColumn
        (⟨(i.castSucc, i.succ), i.castSucc_lt_succ⟩ : UpperEntryPair (n + 1)) =
        i.succ := Fin.ext rfl
    rw [hc] at hp
    simpa only [upperEntryCoordinates_apply] using hp
  simp only [he, Finset.sum_neg_distrib, neg_neg, unipotentFourierSum]

omit [BorelSpace K] [SecondCountableTopology K] [LocallyCompactSpace K] [T2Space K] in
private theorem upper_phase (n : ℕ) (u : upperUnipotent (n + 1) K) (v : Fin n → K) :
    (∑ i : Fin n, (u.val.val * firstColumnMatrix n v) i.castSucc i.succ) =
      unipotentFourierSum n u := by
  apply Finset.sum_congr rfl
  intro i _
  rw [← upperColumnParam_eq_mul]
  exact (upperFreeParam_upperEntry n _
    ⟨(i.castSucc, i.succ), i.castSucc_lt_succ⟩).trans
      (upperEntryCoordinates_apply u ⟨(i.castSucc, i.succ), i.castSucc_lt_succ⟩)

private theorem integral_pullback {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {η : Measure B} {p : A → B} (hp : MeasurePreserving p μ η)
    {f : B → ℂ} (hf : Integrable f η) :
    (∫ x, f (p x) ∂μ) = ∫ y, f y ∂η := by
  have hm : AEStronglyMeasurable f (μ.map p) := hp.map_eq.symm ▸ hf.aestronglyMeasurable
  exact (integral_map hp.measurable.aemeasurable hm).symm.trans
    (by rw [hp.map_eq])

variable [TotallyDisconnectedSpace K]

/-- Fourier inversion on the complementary affine slices, expressed through
actual upper-unipotent matrices with the supplied strict-upper coordinate
product. Both sides are absolutely convergent, including in size one. -/
theorem unipotentCoordinate_fourier_duality (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] (hsd : IsSelfDual ψ ν)
    (n : ℕ) (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) K)) :
    Integrable (fun z : (UpperEntryPair (n + 1) → K) × K =>
      let u := (upperEntryCoordinates (n + 1)).symm z.1
      ψ.complex (unipotentFourierSum n u) *
        rectangularFourierIntegral ψ ν Φ (u.val.val.transpose * cyclicShiftMatrix n z.2))
      ((upperEntryProductMeasure ν (n + 1)).prod ν.measure) ∧
    Integrable (fun z : (UpperEntryPair (n + 1) → K) × (Fin n → K) =>
      let u := (upperEntryCoordinates (n + 1)).symm z.1
      ψ.complex (-unipotentFourierSum n u) * Φ (u.val.val * firstColumnMatrix n z.2))
      ((upperEntryProductMeasure ν (n + 1)).prod (rowMeasure ν n)) ∧
    (∫ z : (UpperEntryPair (n + 1) → K) × K,
      let u := (upperEntryCoordinates (n + 1)).symm z.1
      ψ.complex (unipotentFourierSum n u) *
        rectangularFourierIntegral ψ ν Φ (u.val.val.transpose * cyclicShiftMatrix n z.2)
      ∂(upperEntryProductMeasure ν (n + 1)).prod ν.measure) =
    ∫ z : (UpperEntryPair (n + 1) → K) × (Fin n → K),
      let u := (upperEntryCoordinates (n + 1)).symm z.1
      ψ.complex (-unipotentFourierSum n u) * Φ (u.val.val * firstColumnMatrix n z.2)
      ∂(upperEntryProductMeasure ν (n + 1)).prod (rowMeasure ν n) := by
  obtain ⟨hl, hu, he⟩ := shiftedTriangular_fourier_duality ψ ν hsd n Φ
  have hpl := shiftedLower_transpose_product_preserving ν n
  have hpu := upper_unipotent_product_preserving ν n
  have hil := hpl.integrable_comp_of_integrable hl
  have hiu := hpu.integrable_comp_of_integrable hu
  have hel := integral_pullback hpl hl
  have heu := integral_pullback hpu hu
  dsimp only [Function.comp_def] at hil hiu
  simp only [lower_phase, upper_phase] at hil hiu hel heu
  exact ⟨hil, hiu, hel.trans (he.trans heu.symm)⟩

variable {n : ℕ} [MeasurableSpace (upperUnipotent (n + 1) K)]
  [BorelSpace (upperUnipotent (n + 1) K)]

omit [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K] in
private theorem haar_product_pullback (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (μ : Measure (upperUnipotent (n + 1) K)) (c : ℝ≥0)
    (hμ : μ = c • (upperEntryProductMeasure ν (n + 1)).map
      (upperEntryCoordinates (n + 1)).symm)
    {A : Type*} [MeasurableSpace A] (η : Measure A) [SFinite η]
    (f : upperUnipotent (n + 1) K × A → ℂ)
    (hf : Integrable (fun z : (UpperEntryPair (n + 1) → K) × A =>
      f ((upperEntryCoordinates (n + 1)).symm z.1, z.2))
      ((upperEntryProductMeasure ν (n + 1)).prod η)) :
    Integrable f (μ.prod η) ∧
    (∫ z, f z ∂μ.prod η) = (c : ℂ) *
      ∫ z : (UpperEntryPair (n + 1) → K) × A,
        f ((upperEntryCoordinates (n + 1)).symm z.1, z.2)
        ∂(upperEntryProductMeasure ν (n + 1)).prod η := by
  let e := upperEntryCoordinates (n + 1) (K := K)
  let μ₀ := (upperEntryProductMeasure ν (n + 1)).map e.symm
  let q := e.symm.toMeasurableEquiv.prodCongr (MeasurableEquiv.refl A)
  have hp₀ : MeasurePreserving e.symm (upperEntryProductMeasure ν (n + 1)) μ₀ :=
    ⟨e.symm.measurable, rfl⟩
  have hp : MeasurePreserving q
      ((upperEntryProductMeasure ν (n + 1)).prod η) (μ₀.prod η) :=
    hp₀.prod (MeasurePreserving.id η)
  have hfi : Integrable f (μ₀.prod η) :=
    (hp.integrable_comp_emb q.measurableEmbedding).mp hf
  rw [hμ, Measure.prod_smul_left]
  refine ⟨hfi.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure]
  rw [← hp.integral_comp q.measurableEmbedding f]
  simp only [NNReal.smul_def, Complex.real_smul]
  rfl

/-- The Fourier identity for any actual upper-unipotent Haar measure. Its
normalization need not agree with the coordinate product: the same Haar scalar
multiplies the two absolutely convergent sides. -/
theorem unipotentHaar_transpose_fourier_duality (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] (hsd : IsSelfDual ψ ν)
    (μ : Measure (upperUnipotent (n + 1) K)) [μ.IsHaarMeasure]
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) K)) :
    Integrable (fun z : upperUnipotent (n + 1) K × K =>
      ψ.complex (unipotentFourierSum n z.1) * rectangularFourierIntegral ψ ν Φ
        (z.1.val.val.transpose * cyclicShiftMatrix n z.2)) (μ.prod ν.measure) ∧
    Integrable (fun z : upperUnipotent (n + 1) K × (Fin n → K) =>
      ψ.complex (-unipotentFourierSum n z.1) *
        Φ (z.1.val.val * firstColumnMatrix n z.2)) (μ.prod (rowMeasure ν n)) ∧
    (∫ z : upperUnipotent (n + 1) K × K,
      ψ.complex (unipotentFourierSum n z.1) * rectangularFourierIntegral ψ ν Φ
        (z.1.val.val.transpose * cyclicShiftMatrix n z.2) ∂μ.prod ν.measure) =
    ∫ z : upperUnipotent (n + 1) K × (Fin n → K),
      ψ.complex (-unipotentFourierSum n z.1) *
        Φ (z.1.val.val * firstColumnMatrix n z.2) ∂μ.prod (rowMeasure ν n) := by
  let e := upperEntryCoordinates (n + 1) (K := K)
  let μ₀ := (upperEntryProductMeasure ν (n + 1)).map e.symm
  let : μ₀.IsHaarMeasure := upperEntryProductMeasure_isHaar ν
  let : LocallyCompactSpace (upperUnipotent (n + 1) K) :=
    e.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology (upperUnipotent (n + 1) K) := e.secondCountableTopology
  let c := Measure.haarScalarFactor μ μ₀
  have hμ : μ = c • μ₀ := Measure.isMulLeftInvariant_eq_smul μ μ₀
  obtain ⟨hl, hu, he⟩ := unipotentCoordinate_fourier_duality ψ ν hsd n Φ
  obtain ⟨hl', hel⟩ := haar_product_pullback ν μ c hμ ν.measure
    (fun z : upperUnipotent (n + 1) K × K =>
      ψ.complex (unipotentFourierSum n z.1) * rectangularFourierIntegral ψ ν Φ
        (z.1.val.val.transpose * cyclicShiftMatrix n z.2)) hl
  obtain ⟨hu', heu⟩ := haar_product_pullback ν μ c hμ (rowMeasure ν n)
    (fun z : upperUnipotent (n + 1) K × (Fin n → K) =>
      ψ.complex (-unipotentFourierSum n z.1) *
        Φ (z.1.val.val * firstColumnMatrix n z.2)) hu
  exact ⟨hl', hu', hel.trans ((congrArg (fun t : ℂ => (c : ℂ) * t) he).trans heu.symm)⟩

end Langlands.HarmonicAnalysis
