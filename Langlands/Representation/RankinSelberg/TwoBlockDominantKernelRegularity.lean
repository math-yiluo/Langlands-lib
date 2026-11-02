import Langlands.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData
import Langlands.Representation.RankinSelberg.TwoBlockLowerIntegrandRegularity
import Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionReduction
import Langlands.Analysis.Local.QuotientKernelSupport
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Regularity of the actual dominant rectangle kernel

The raw weighted kernel is continuous for smooth coefficient-image tests.
Its total rectangle averages and the set of integrable rectangle fibers are
measurable, both on representatives and on the lower quotient.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockLowerUnipotentQuotient TwoBlockLowerUnfolding QuotientIntegration

universe uF uV uW

section Matrices

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
variable {t r j k : ℕ} {m : Fin 2 → ℕ}
variable (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))

/-- Joint continuity of the two actual rectangle insertions, including zero
rectangle dimensions. -/
theorem continuous_rectangleUnipotent :
    Continuous (fun z : Rectangles m j k K => rectangleUnipotent h hr z.1 z.2) := by
  have hv : Continuous (fun z : Rectangles m j k K =>
      (rectangleUnipotent h hr z.1 z.2).val) := by
    apply continuous_matrix
    intro i l
    obtain ⟨i, rfl⟩ := (coordinates h hr).surjective i
    obtain ⟨l, rfl⟩ := (coordinates h hr).surjective l
    simp only [rectangleUnipotent_five_entry]
    rcases i with i | ((i | (i | i)) | i) <;>
      rcases l with l | ((l | (l | l)) | l) <;>
        simp only [rectangleEntries]
    all_goals first
      | exact continuous_const
      | exact (continuous_apply l).comp ((continuous_apply i).comp continuous_fst)
      | exact (continuous_apply l).comp ((continuous_apply i).comp continuous_snd)
  apply Units.continuous_iff.mpr
  refine ⟨hv, ?_⟩
  simpa only [rectangleUnipotent_inv, Function.comp_def, Pi.neg_apply] using
    hv.comp (continuous_fst.neg.prodMk continuous_snd.neg)

omit [IsTopologicalRing K] in
/-- Continuity of the actual rank inclusion used by the dominant matrix. -/
theorem continuous_append :
    Continuous (append (K := K) hr) := by
  exact (reindexContinuous (R := K) (finCongr (congrArg (· + 1) hr.symm))).continuous.comp
    (SquareIntegrableWhittakerRestriction.continuous_appendIdentity t (j + k + 1))

/-- Joint continuity in the group coordinate and both source rectangles. -/
theorem continuous_matrix :
    Continuous (fun z : GeneralLinear (t + 1) K × Rectangles m j k K =>
      matrix h hr z.1 z.2.1 z.2.2) := by
  exact ((continuous_const.mul ((continuous_rectangleUnipotent h hr).comp
    continuous_snd)).mul continuous_const).mul
      ((continuous_append hr).comp continuous_fst)

end Matrices

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance kernelRegularityTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance kernelRegularityValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance kernelRegularityLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance kernelRegularityT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance kernelRegularitySecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance kernelRegularityMeasurable : MeasurableSpace F.Carrier := borel _
local instance kernelRegularityBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance kernelRegularityMatrixBorel (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F.Carrier))
local instance kernelRegularityMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F.Carrier))
local instance kernelRegularityRectanglesBorel (m : Fin 2 → ℕ) (j k : ℕ) :
    BorelSpace (Rectangles m j k F.Carrier) :=
  inferInstanceAs (BorelSpace (Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier ×
    Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier))
local instance kernelRegularityGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance kernelRegularityGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance kernelRegularityGLSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance kernelRegularityGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n

variable {t r j k : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ν : AdditiveHaarMeasure F.Carrier)
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
variable (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
variable (Wtest : (coefficientModel π lambda).toSubmodule)

include hπ

/-- Smoothness alone gives joint continuity of the actual weighted raw kernel,
with no absolute-integrability premise. -/
theorem continuous_kernel (hr : r = t + (j + k + 1)) (s : ℂ) :
    Continuous (fun z : GeneralLinear (t + 1) F.Carrier × Rectangles m j k F.Carrier =>
      kernel ell f Wtest.val hr s z.1 z.2.1 z.2.2) := by
  have hf := (scalarSection_locallyConstant (fun i => (ell i).val) f 1).continuous
  have hW := (coefficient_locallyConstant π hπ lambda Wtest).continuous
  exact ((hf.comp continuous_fst).mul (hW.comp (continuous_matrix h hr))).mul
    ((continuous_adjacentRank_determinantWeight F (t + 1)
      (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ))).comp continuous_fst)

/-- The actual weighted raw kernel bundled with its joint continuity proof. -/
def continuousKernel (hr : r = t + (j + k + 1)) (s : ℂ) :
    C(GeneralLinear (t + 1) F.Carrier × Rectangles m j k F.Carrier, ℂ) :=
  ⟨_, continuous_kernel ell f π hπ lambda Wtest hr s⟩

@[simp] theorem continuousKernel_apply (hr : r = t + (j + k + 1)) (s : ℂ)
    (z : GeneralLinear (t + 1) F.Carrier × Rectangles m j k F.Carrier) :
    continuousKernel ell f π hπ lambda Wtest hr s z =
      kernel ell f Wtest.val hr s z.1 z.2.1 z.2.2 := rfl

/-- The complex total rectangle integral is measurable even when some fibers
are not integrable. -/
theorem measurable_representativeKernel (hr : r = t + (j + k + 1)) (s : ℂ) :
    Measurable (representativeKernel ν ell f Wtest.val hr s) :=
  (continuous_kernel ell f π hπ lambda Wtest hr s).measurable.stronglyMeasurable
    |>.integral_prod_right' |>.measurable

/-- Measurability concerns the integral of the raw norm, retaining the exact
supplied rectangle Haar measure. -/
theorem measurable_representativeNormProfile (hr : r = t + (j + k + 1)) (s : ℂ) :
    Measurable (representativeNormProfile ν ell f Wtest.val hr s) :=
  (continuous_kernel ell f π hπ lambda Wtest hr s).norm.measurable.stronglyMeasurable
    |>.integral_prod_right' |>.measurable

/-- Actual rectangle-fiber integrability defines a measurable set of group
representatives. -/
theorem measurableSet_fiberIntegrable (hr : r = t + (j + k + 1)) (s : ℂ) :
    MeasurableSet {g | FiberIntegrable ν ell f Wtest.val hr s g} :=
  measurableSet_integrable
    (continuous_kernel ell f π hπ lambda Wtest hr s).measurable.stronglyMeasurable

variable [MeasurableSpace (LowerQuotient h F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)]

/-- Measurability of the actual complex average descends without choosing
representatives. -/
theorem measurable_quotientKernel (hr : r = t + (j + k + 1)) (s : ℂ) :
    Measurable (quotientKernel ν ell f Wtest.val hr s) := by
  apply (measurable_quotient_iff _ (isClosed_lowerBlockUnipotent_canonical F h) _).2
  exact measurable_representativeKernel ν ell f π hπ lambda Wtest hr s

/-- The actual real raw-norm profile is measurable on the lower quotient. -/
theorem measurable_quotientNormProfile (hr : r = t + (j + k + 1)) (s : ℂ) :
    Measurable (quotientNormProfile ν ell f Wtest.val hr s) := by
  apply (measurable_quotient_iff _ (isClosed_lowerBlockUnipotent_canonical F h) _).2
  exact measurable_representativeNormProfile ν ell f π hπ lambda Wtest hr s

/-- Actual rectangle-fiber integrability is a measurable condition on the
quotient, with no assertion that it holds almost everywhere. -/
theorem measurableSet_quotientFiberIntegrable (hr : r = t + (j + k + 1)) (s : ℂ) :
    MeasurableSet {q | quotientFiberIntegrable ν ell f Wtest.val hr s q} := by
  apply measurableSet_setOfPred.mpr
  apply (measurable_quotient_iff _ (isClosed_lowerBlockUnipotent_canonical F h) _).2
  exact measurableSet_setOfPred.mp
    (measurableSet_fiberIntegrable ν ell f π hπ lambda Wtest hr s)

end Langlands.RankinSelberg.TwoBlockDominantRectangular
