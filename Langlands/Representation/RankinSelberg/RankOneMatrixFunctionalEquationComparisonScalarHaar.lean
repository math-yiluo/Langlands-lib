import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive

/-! The exact scalar additive measure and the naturally weighted GL₁ Haar. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uH

section ScalarMeasure

variable {K : Type uF} [Field K] [TopologicalSpace K] [MeasurableSpace K]

/-- Evaluation of the only matrix entry as an actual measurable equivalence. -/
def oneByOneScalarEquiv : Matrix (Fin 1) (Fin 1) K ≃ᵐ K :=
  (MeasurableEquiv.piUnique (fun _ : Fin 1 => Fin 1 → K)).trans
    (MeasurableEquiv.piUnique (fun _ : Fin 1 => K))

omit [Field K] [TopologicalSpace K] in
@[simp] theorem oneByOneScalarEquiv_apply (A : Matrix (Fin 1) (Fin 1) K) :
    oneByOneScalarEquiv A = A 0 0 := rfl

/-- No normalization is introduced by evaluating the unique matrix entry. -/
theorem oneByOneScalarEquiv_measurePreserving (ν : AdditiveHaarMeasure K) :
    MeasurePreserving (oneByOneScalarEquiv (K := K))
      (rectangularMeasure ν 1 1) ν.measure :=
  (measurePreserving_piUnique (fun _ : Fin 1 => ν.measure)).comp
    (measurePreserving_piUnique (fun _ : Fin 1 => Measure.pi (fun _ : Fin 1 => ν.measure)))

/-- In size one only the zero scalar is excluded by matrix invertibility. -/
theorem rectangularMeasure_one_restrict_invertible
    (ν : AdditiveHaarMeasure K) [NullSingletonClass ν.measure] :
    (rectangularMeasure ν 1 1).restrict
      (Set.range (Units.val : Langlands.GeneralLinear 1 K → Matrix (Fin 1) (Fin 1) K)) =
        rectangularMeasure ν 1 1 := by
  apply Measure.restrict_eq_self_of_ae_mem
  have hn := (oneByOneScalarEquiv_measurePreserving ν).quasiMeasurePreserving.ae
    (ν.measure.ae_ne 0)
  filter_upwards [hn] with A hA
  change ∃ g : Langlands.GeneralLinear 1 K, g.val = A
  apply (Matrix.isUnit_iff_isUnit_det A).2
  rw [Matrix.det_fin_one]
  exact isUnit_iff_ne_zero.mpr hA

end ScalarMeasure

section CanonicalPadic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance scalarHaarTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance scalarHaarValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance scalarHaarLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance scalarHaarT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance scalarHaarSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance scalarHaarSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance scalarHaarMeasurable : MeasurableSpace F.Carrier := borel _
local instance scalarHaarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance scalarHaarGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance scalarHaarGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance scalarHaarGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance scalarHaarGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance scalarHaarNullSingleton (ν : AdditiveHaarMeasure F.Carrier) :
    NullSingletonClass ν.measure := by
  have : (nhdsWithin (0 : F.Carrier) {0}ᶜ).NeBot := by
    let := F.canonicalNormedField
    exact NormedField.nhdsNE_neBot 0
  infer_instance

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The natural determinant exponent one transports genuine scalar convergence
for every complex function, with the supplied additive Haar normalization. -/
theorem integrable_generalLinear_one_natWeight_iff
    (ν : AdditiveHaarMeasure F.Carrier) (A : F.Carrier → ℂ) :
    Integrable (fun g : Langlands.GeneralLinear 1 F.Carrier =>
      determinantWeight abv g 1 * A (g 0 0)) (generalLinearHaar F.Carrier 0) ↔
        Integrable A ν.measure := by
  have h := GLDeterminantDensity.integrable_generalLinearHaar_natWeight_iff F ν 0
    (fun X => A (X 0 0))
  rw [rectangularMeasure_one_restrict_invertible ν] at h
  simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using
    h.trans ((oneByOneScalarEquiv_measurePreserving ν).integrable_comp_emb
      oneByOneScalarEquiv.measurableEmbedding)

/-- The fixed normalization scalar is independent of the scalar integrand. -/
theorem integral_generalLinear_one_natWeight
    (ν : AdditiveHaarMeasure F.Carrier) (A : F.Carrier → ℂ) :
    (∫ g : Langlands.GeneralLinear 1 F.Carrier,
      determinantWeight abv g 1 * A (g 0 0) ∂generalLinearHaar F.Carrier 0) =
    ((GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ *
      ∫ a, A a ∂ν.measure := by
  have h := GLDeterminantDensity.integral_generalLinearHaar_natWeight F ν 0
    (fun X => A (X 0 0))
  rw [rectangularMeasure_one_restrict_invertible ν] at h
  have he := (oneByOneScalarEquiv_measurePreserving ν).integral_comp
    oneByOneScalarEquiv.measurableEmbedding A
  change (∫ X : Matrix (Fin 1) (Fin 1) F.Carrier, A (X 0 0)
    ∂rectangularMeasure ν 1 1) = _ at he
  rw [he] at h
  simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using h

/-- Scalar density cancellation holds on the full product with any auxiliary
s-finite parameter measure. -/
theorem integrable_prod_generalLinear_one_natWeight_iff
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F.Carrier) (A : H × F.Carrier → ℂ) :
    Integrable (fun z : H × Langlands.GeneralLinear 1 F.Carrier =>
      determinantWeight abv z.2 1 * A (z.1, z.2 0 0))
      (μH.prod (generalLinearHaar F.Carrier 0)) ↔
        Integrable A (μH.prod ν.measure) := by
  have h := GLDeterminantDensity.integrable_prod_generalLinearHaar_natWeight_iff
    F μH ν 0 (fun z => A (z.1, z.2 0 0))
  rw [rectangularMeasure_one_restrict_invertible ν] at h
  let e := (MeasurableEquiv.refl H).prodCongr (oneByOneScalarEquiv (K := F.Carrier))
  have hp : MeasurePreserving e (μH.prod (rectangularMeasure ν 1 1))
      (μH.prod ν.measure) :=
    (MeasurePreserving.id μH).prod (oneByOneScalarEquiv_measurePreserving ν)
  simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using
    h.trans (hp.integrable_comp_emb e.measurableEmbedding)

/-- Product integrals have the same normalization scalar as scalar integrals. -/
theorem integral_prod_generalLinear_one_natWeight
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F.Carrier) (A : H × F.Carrier → ℂ) :
    (∫ z : H × Langlands.GeneralLinear 1 F.Carrier,
      determinantWeight abv z.2 1 * A (z.1, z.2 0 0)
      ∂μH.prod (generalLinearHaar F.Carrier 0)) =
    ((GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ *
      ∫ z, A z ∂μH.prod ν.measure := by
  have h := GLDeterminantDensity.integral_prod_generalLinearHaar_natWeight
    F μH ν 0 (fun z => A (z.1, z.2 0 0))
  rw [rectangularMeasure_one_restrict_invertible ν] at h
  let e := (MeasurableEquiv.refl H).prodCongr (oneByOneScalarEquiv (K := F.Carrier))
  have hp : MeasurePreserving e (μH.prod (rectangularMeasure ν 1 1))
      (μH.prod ν.measure) :=
    (MeasurePreserving.id μH).prod (oneByOneScalarEquiv_measurePreserving ν)
  have he := hp.integral_comp e.measurableEmbedding A
  change (∫ z : H × Matrix (Fin 1) (Fin 1) F.Carrier,
    A (z.1, z.2 0 0) ∂μH.prod (rectangularMeasure ν 1 1)) = _ at he
  rw [he] at h
  simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using h

/-- Full joint convergence with the scalar or GL₁ variable first. -/
theorem integrable_generalLinear_one_prod_natWeight_iff
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F.Carrier) (A : F.Carrier × H → ℂ) :
    Integrable (fun z : Langlands.GeneralLinear 1 F.Carrier × H =>
      determinantWeight abv z.1 1 * A (z.1 0 0, z.2))
      ((generalLinearHaar F.Carrier 0).prod μH) ↔
        Integrable A (ν.measure.prod μH) := by
  have h := integrable_prod_generalLinear_one_natWeight_iff F μH ν
    (fun z => A (z.2, z.1))
  constructor
  · intro hi
    exact (h.mp hi.swap).swap
  · intro hi
    exact (h.mpr hi.swap).swap

/-- Scalar-first product integral transport with the identical fixed scalar. -/
theorem integral_generalLinear_one_prod_natWeight
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F.Carrier) (A : F.Carrier × H → ℂ) :
    (∫ z : Langlands.GeneralLinear 1 F.Carrier × H,
      determinantWeight abv z.1 1 * A (z.1 0 0, z.2)
      ∂(generalLinearHaar F.Carrier 0).prod μH) =
    ((GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ *
      ∫ z, A z ∂ν.measure.prod μH := by
  calc
    _ = ∫ z : H × Langlands.GeneralLinear 1 F.Carrier,
        determinantWeight abv z.2 1 * A (z.2 0 0, z.1)
        ∂μH.prod (generalLinearHaar F.Carrier 0) := (integral_prod_swap _).symm
    _ = _ := (integral_prod_generalLinear_one_natWeight F μH ν
        (fun z => A (z.2, z.1))).trans
      (congrArg (fun c : ℂ =>
        ((GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ * c)
        (integral_prod_swap A))

end CanonicalPadic

end Langlands.RankinSelberg
