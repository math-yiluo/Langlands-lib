import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota
/-!
# The reflection `[v] ↦ [w v^ι]` of the small quotient

On `N \ GL_(n+1)` the map `[v] ↦ [w v^ι]`, with `w` the long Weyl element and `ι` the
inverse transpose, is a well-defined involutive homeomorphism. It preserves every
compatible quotient measure and exchanges the determinant slices `k` and `-k`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding measurePreserving_reflectionQuotient reflectionQuotient_mem_determinantSlice setIntegral_determinantSlice_reflectionQuotient
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory MeasureTheory.Measure
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.Whittaker
open scoped NNReal ENNReal

universe uG uK uF

section Reflection


end Reflection

section Determinant


end Determinant

section Padic

variable (F : Type uF) [Field F]

/-- The reflection exchanges the determinant slices `k` and `-k`. -/
theorem reflectionQuotient_mem_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ) (k : ℤ) :
    ∀ q : LeftUnipotentQuotient n F,
      reflectionQuotient n q ∈ determinantSlice (⟨⟩ : LocalFieldData F) n k ↔
        q ∈ determinantSlice (⟨⟩ : LocalFieldData F) n (-k) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [reflectionQuotient_mk, mk_mem_determinantSlice_iff_normalizedAbs,
      mk_mem_determinantSlice_iff_normalizedAbs]
    have habs := abv_det_weylLong_mul_inverseTranspose (normalizedAbsoluteValue T) g
    change T.normalizedAbs (Matrix.det (weylLong (n + 1) F *
      inverseTranspose (n + 1) F g).val) = _ ↔
        T.normalizedAbs (Matrix.det g.val) = _
    change T.normalizedAbs _ = (T.normalizedAbs _)⁻¹ at habs
    rw [habs, neg_neg]
    have hq : (0 : ℝ) < T.residueCardinality := by
      exact_mod_cast (Nat.zero_lt_one.trans T.residueCardinality_gt_one)
    constructor
    · intro he
      rw [← inv_inv (T.normalizedAbs _), he, zpow_neg, inv_inv]
    · intro he
      rw [he, zpow_neg]

/-- The reflection preserves every compatible quotient measure on the small quotient. -/
theorem measurePreserving_reflectionQuotient [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup (n + 1)
    letI : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ νA : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) νA →
      MeasurePreserving (reflectionQuotient n) νA νA := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (n + 1)
  let : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro νA hA
  have := T.fieldT2
  have := T.generalLinearLocallyCompactSpace (n + 1)
  have := T.generalLinearT2Space (n + 1)
  have hclosed : IsClosed (upperUnipotent (n + 1) F : Set (GeneralLinear (n + 1) F)) :=
    UpperUnipotent.isClosed
  have hscale := compatibleQuotientAutomorphismScaling
    (upperUnipotent (n + 1) F) hclosed (generalLinearHaar F n)
    (unipotentHaar F n) νA hA (reflectionAut n) (reflectionAut_mem_iff n)
  dsimp only at hscale
  obtain ⟨hmap, -⟩ := hscale
  have : LocallyCompactSpace (upperUnipotent (n + 1) F) := hclosed.locallyCompactSpace
  rw [mulEquivHaarChar_eq_one_of_involutive (reflectionAut n) (reflectionAut_involutive n),
    mulEquivHaarChar_eq_one_of_involutive _ (fun x => Subtype.ext (reflectionAut_involutive n x.val)),
    div_one, ENNReal.coe_one, one_smul] at hmap
  exact (hA.right_invariant (weylLong (n + 1) F)).comp
    ⟨(quotientAutomorphism _ (reflectionAut n) (reflectionAut_mem_iff n)).continuous.measurable,
      hmap⟩

/-- Change of variables by the reflection on determinant slices. -/
theorem setIntegral_determinantSlice_reflectionQuotient [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ) (k : ℤ) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup (n + 1)
    letI : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ νA : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) νA →
      ∀ (f : LeftUnipotentQuotient n F → ℂ),
        (∫ q in determinantSlice T n k, f q ∂νA) =
          ∫ q in determinantSlice T n (-k), f (reflectionQuotient n q) ∂νA := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (n + 1)
  let : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro νA hA f
  have hmp := measurePreserving_reflectionQuotient F n νA hA
  rw [← hmp.setIntegral_preimage_emb (reflectionQuotient n).measurableEmbedding f
    (determinantSlice T n k)]
  have hpre : reflectionQuotient n ⁻¹' determinantSlice T n k = determinantSlice T n (-k) :=
    Set.ext (reflectionQuotient_mem_determinantSlice F n k)
  rw [hpre]

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
