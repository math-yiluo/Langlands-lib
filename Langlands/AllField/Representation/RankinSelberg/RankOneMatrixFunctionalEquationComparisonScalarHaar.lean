import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive
import Langlands.LocalField.NonzeroParameter
/-! The exact scalar additive measure and the naturally weighted GL₁ Haar. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support integrable_generalLinear_one_natWeight_iff integrable_generalLinear_one_prod_natWeight_iff integrable_prod_generalLinear_one_natWeight_iff integral_generalLinear_one_natWeight integral_generalLinear_one_prod_natWeight integral_prod_generalLinear_one_natWeight lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues scalarHaarBorel scalarHaarGLBorel scalarHaarGLLocallyCompact scalarHaarGLMeasurable scalarHaarGLSecondCountable scalarHaarLocalField scalarHaarMeasurable scalarHaarNullSingleton scalarHaarSecondCountable scalarHaarSigmaCompact scalarHaarT2 scalarHaarTopology scalarHaarValuativeRel singleton_modulus_real zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear

universe uF uH

section ScalarMeasure

variable {K : Type uF} [Field K] [TopologicalSpace K] [MeasurableSpace K]

end ScalarMeasure

section CanonicalPadic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance scalarHaarT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance scalarHaarSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance scalarHaarSigmaCompact : SigmaCompactSpace F :=
  (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance scalarHaarMeasurable : MeasurableSpace F := borel _
local instance scalarHaarBorel : BorelSpace F := ⟨rfl⟩
local instance scalarHaarGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance scalarHaarGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance scalarHaarGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance scalarHaarGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance scalarHaarNullSingleton (ν : AdditiveHaarMeasure F) :
    NullSingletonClass ν.measure := by
  have : (nhdsWithin (0 : F) {0}ᶜ).NeBot := by
    exact Langlands.LocalField.nhdsNE_zero_neBot F
  infer_instance

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The natural determinant exponent one transports genuine scalar convergence
for every complex function, with the supplied additive Haar normalization. -/
theorem integrable_generalLinear_one_natWeight_iff
    (ν : AdditiveHaarMeasure F) (A : F → ℂ) :
    Integrable (fun g : Langlands.GeneralLinear 1 F =>
      determinantWeight abv g 1 * A (g 0 0)) (generalLinearHaar F 0) ↔
        Integrable A ν.measure := by
  have h := Langlands.AllField.RankinSelberg.GLDeterminantDensity.integrable_generalLinearHaar_natWeight_iff F ν 0
    (fun X => A (X 0 0))
  rw [rectangularMeasure_one_restrict_invertible ν] at h
  simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using
    h.trans ((oneByOneScalarEquiv_measurePreserving ν).integrable_comp_emb
      oneByOneScalarEquiv.measurableEmbedding)

/-- The fixed normalization scalar is independent of the scalar integrand. -/
theorem integral_generalLinear_one_natWeight
    (ν : AdditiveHaarMeasure F) (A : F → ℂ) :
    (∫ g : Langlands.GeneralLinear 1 F,
      determinantWeight abv g 1 * A (g 0 0) ∂generalLinearHaar F 0) =
    ((Langlands.AllField.RankinSelberg.GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ *
      ∫ a, A a ∂ν.measure := by
  have h := Langlands.AllField.RankinSelberg.GLDeterminantDensity.integral_generalLinearHaar_natWeight F ν 0
    (fun X => A (X 0 0))
  rw [rectangularMeasure_one_restrict_invertible ν] at h
  have he := (oneByOneScalarEquiv_measurePreserving ν).integral_comp
    oneByOneScalarEquiv.measurableEmbedding A
  change (∫ X : Matrix (Fin 1) (Fin 1) F, A (X 0 0)
    ∂rectangularMeasure ν 1 1) = _ at he
  rw [he] at h
  simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using h

/-- Scalar density cancellation holds on the full product with any auxiliary
s-finite parameter measure. -/
theorem integrable_prod_generalLinear_one_natWeight_iff
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F) (A : H × F → ℂ) :
    Integrable (fun z : H × Langlands.GeneralLinear 1 F =>
      determinantWeight abv z.2 1 * A (z.1, z.2 0 0))
      (μH.prod (generalLinearHaar F 0)) ↔
        Integrable A (μH.prod ν.measure) := by
  have h := Langlands.AllField.RankinSelberg.GLDeterminantDensity.integrable_prod_generalLinearHaar_natWeight_iff
    F μH ν 0 (fun z => A (z.1, z.2 0 0))
  rw [rectangularMeasure_one_restrict_invertible ν] at h
  let e := (MeasurableEquiv.refl H).prodCongr (oneByOneScalarEquiv (K := F))
  have hp : MeasurePreserving e (μH.prod (rectangularMeasure ν 1 1))
      (μH.prod ν.measure) :=
    (MeasurePreserving.id μH).prod (oneByOneScalarEquiv_measurePreserving ν)
  simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using
    h.trans (hp.integrable_comp_emb e.measurableEmbedding)

/-- Product integrals have the same normalization scalar as scalar integrals. -/
theorem integral_prod_generalLinear_one_natWeight
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F) (A : H × F → ℂ) :
    (∫ z : H × Langlands.GeneralLinear 1 F,
      determinantWeight abv z.2 1 * A (z.1, z.2 0 0)
      ∂μH.prod (generalLinearHaar F 0)) =
    ((Langlands.AllField.RankinSelberg.GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ *
      ∫ z, A z ∂μH.prod ν.measure := by
  have h := Langlands.AllField.RankinSelberg.GLDeterminantDensity.integral_prod_generalLinearHaar_natWeight
    F μH ν 0 (fun z => A (z.1, z.2 0 0))
  rw [rectangularMeasure_one_restrict_invertible ν] at h
  let e := (MeasurableEquiv.refl H).prodCongr (oneByOneScalarEquiv (K := F))
  have hp : MeasurePreserving e (μH.prod (rectangularMeasure ν 1 1))
      (μH.prod ν.measure) :=
    (MeasurePreserving.id μH).prod (oneByOneScalarEquiv_measurePreserving ν)
  have he := hp.integral_comp e.measurableEmbedding A
  change (∫ z : H × Matrix (Fin 1) (Fin 1) F,
    A (z.1, z.2 0 0) ∂μH.prod (rectangularMeasure ν 1 1)) = _ at he
  rw [he] at h
  simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using h

/-- Full joint convergence with the scalar or GL₁ variable first. -/
theorem integrable_generalLinear_one_prod_natWeight_iff
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F) (A : F × H → ℂ) :
    Integrable (fun z : Langlands.GeneralLinear 1 F × H =>
      determinantWeight abv z.1 1 * A (z.1 0 0, z.2))
      ((generalLinearHaar F 0).prod μH) ↔
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
    (ν : AdditiveHaarMeasure F) (A : F × H → ℂ) :
    (∫ z : Langlands.GeneralLinear 1 F × H,
      determinantWeight abv z.1 1 * A (z.1 0 0, z.2)
      ∂(generalLinearHaar F 0).prod μH) =
    ((Langlands.AllField.RankinSelberg.GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ *
      ∫ z, A z ∂ν.measure.prod μH := by
  calc
    _ = ∫ z : H × Langlands.GeneralLinear 1 F,
        determinantWeight abv z.2 1 * A (z.2 0 0, z.1)
        ∂μH.prod (generalLinearHaar F 0) := (integral_prod_swap _).symm
    _ = _ := (integral_prod_generalLinear_one_natWeight F μH ν
        (fun z => A (z.2, z.1))).trans
      (congrArg (fun c : ℂ =>
        ((Langlands.AllField.RankinSelberg.GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ)⁻¹ * c)
        (integral_prod_swap A))

end CanonicalPadic

end Langlands.AllField.RankinSelberg
