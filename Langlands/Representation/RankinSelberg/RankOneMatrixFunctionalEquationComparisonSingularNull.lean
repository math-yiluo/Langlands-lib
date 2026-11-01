import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # The singular matrix locus has additive Haar measure zero -/

noncomputable section

namespace Langlands.RankinSelberg.GLDeterminantDensity

open MeasureTheory HarmonicAnalysis Topology
open scoped NNReal ENNReal

universe uK uF

section General

variable {K : Type uK} [Field K]

/-- The determinant-zero locus in the full square matrix space. -/
def singularLocus (r : ℕ) : Set (Matrix (Fin r) (Fin r) K) :=
  {X | X.det = 0}

/-- Scalar translates of a fixed square matrix are singular at only finitely
many scalars, by the monic characteristic polynomial. -/
theorem finite_singular_scalar_translates (r : ℕ)
    (X : Matrix (Fin r) (Fin r) K) :
    Set.Finite {t : K | (Matrix.scalar (Fin r) t + X).det = 0} := by
  have h := Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-X)).ne_zero
  simpa only [Polynomial.IsRoot, Matrix.eval_charpoly, sub_neg_eq_add] using h

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]

/-- Fubini along scalar translates, followed by additive translation invariance,
shows that almost every square matrix is invertible. -/
theorem ae_det_ne_zero_of_addInvariant (r : ℕ)
    (ν : Measure K) [SFinite ν] [NeZero ν] [NullSingletonClass ν]
    (μ : Measure (Matrix (Fin r) (Fin r) K)) [SFinite μ]
    [μ.IsAddLeftInvariant] :
    ∀ᵐ X ∂μ, X.det ≠ 0 := by
  have hf : ∀ᵐ X ∂μ, ∀ᵐ t ∂ν, (Matrix.scalar (Fin r) t + X).det ≠ 0 := by
    exact Filter.Eventually.of_forall fun X =>
      (finite_singular_scalar_translates r X).countable.ae_notMem ν
  have hc : Continuous (fun z : Matrix (Fin r) (Fin r) K × K =>
      (Matrix.scalar (Fin r) z.2 + z.1).det) := by
    apply Continuous.matrix_det
    apply Continuous.add _ continuous_fst
    apply continuous_matrix
    intro i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> fun_prop
  have hm : MeasurableSet {z : Matrix (Fin r) (Fin r) K × K |
      (Matrix.scalar (Fin r) z.2 + z.1).det ≠ 0} :=
    (isOpen_ne_fun hc continuous_const).measurableSet
  obtain ⟨t, ht⟩ := ((Measure.ae_ae_comm hm).mp hf).exists
  exact (eventually_add_left_iff μ (Matrix.scalar (Fin r) t)).mp ht

end General

section CanonicalPadic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance singularNullTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance singularNullValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance singularNullLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance singularNullT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance singularNullSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance singularNullSigmaCompact : SigmaCompactSpace F.Carrier := F.canonicalTopologicalData.sigmaCompactSpace
local instance singularNullMeasurableSpace : MeasurableSpace F.Carrier := borel _
local instance singularNullBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance singularNullPuncturedNhds : (𝓝[≠] (0 : F.Carrier)).NeBot :=
  @NormedField.nhdsNE_neBot F.Carrier F.canonicalNormedField 0

/-- The genuine rectangular product of the supplied scalar additive Haar measure
assigns measure zero to the singular locus, in every square size. -/
theorem rectangularMeasure_ae_det_ne_zero (ν : AdditiveHaarMeasure F.Carrier) (r : ℕ) :
    ∀ᵐ X ∂rectangularMeasure ν r r, X.det ≠ 0 := by
  exact ae_det_ne_zero_of_addInvariant r ν.measure (rectangularMeasure ν r r)

/-- The singular matrix locus is null for the supplied product Haar measure. -/
theorem rectangularMeasure_singularLocus (ν : AdditiveHaarMeasure F.Carrier) (r : ℕ) :
    rectangularMeasure ν r r (singularLocus (K := F.Carrier) r) = 0 := by
  simpa only [ae_iff, singularLocus, not_not] using
    rectangularMeasure_ae_det_ne_zero F ν r

/-- Restricting the supplied additive matrix Haar measure to the actual range
of the GL inclusion does not change that measure. -/
theorem rectangularMeasure_restrict_generalLinear (ν : AdditiveHaarMeasure F.Carrier)
    (r : ℕ) :
    (rectangularMeasure ν r r).restrict
      (Set.range (Units.val : Langlands.GeneralLinear r F.Carrier →
        Matrix (Fin r) (Fin r) F.Carrier)) = rectangularMeasure ν r r := by
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [rectangularMeasure_ae_det_ne_zero F ν r] with X hX
  exact ((Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr hX))

end CanonicalPadic

end Langlands.RankinSelberg.GLDeterminantDensity
