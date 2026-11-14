import Langlands.Representation.RankinSelberg.AdjacentRankDeterminantShells
import Langlands.AllField.Representation.GodementJacquet.Zeta
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof
/-! Compact inner determinant slices for the calculation of JPSS Section 6.3. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The actual general-linear determinant slice, before taking a unipotent quotient. -/
def generalLinearDeterminantSlice (r : ℕ) (m : ℤ) :
    Set (Langlands.GeneralLinear (r + 1) F) :=
  {h | T.ord (GeneralLinear.determinant h : F) = m}

@[simp] theorem mem_generalLinearDeterminantSlice {r : ℕ} {m : ℤ}
    {h : Langlands.GeneralLinear (r + 1) F} :
    h ∈ generalLinearDeterminantSlice T r m ↔
      T.ord (GeneralLinear.determinant h : F) = m := Iff.rfl

theorem isClopen_generalLinearDeterminantSlice (r : ℕ) (m : ℤ) :
    letI := T.topology
    IsClopen (generalLinearDeterminantSlice T r m) := by
  let := T.topology
  exact (isClopen_discrete ({m} : Set ℤ)).preimage
    ((continuous_ord_units T).comp (T.generalLinearDeterminant (r + 1)).continuous)

/-- On the group slice, normalized determinant absolute value has the required
strictly positive constant value. -/
theorem normalizedAbs_det_of_mem_generalLinearDeterminantSlice {r : ℕ} {m : ℤ}
    {h : Langlands.GeneralLinear (r + 1) F}
    (hh : h ∈ generalLinearDeterminantSlice T r m) :
    T.normalizedAbs (Matrix.det h.val) = (T.residueCardinality : ℝ) ^ (-m) := by
  change T.normalizedAbs (GeneralLinear.determinant h : F) = _
  rw [T.normalizedAbs_of_ne_zero (GeneralLinear.determinant h).ne_zero, hh]

/-- A compact full-matrix test, cut out by a fixed determinant slice, has compact
support on the actual general linear group. No bound on a coefficient is needed. -/
theorem hasCompactSupport_matrixSlice (r : ℕ) :
    letI := T.topology
    ∀ (Φ : GodementJacquet.MatrixTestFunction r F) (m : ℤ),
      HasCompactSupport ((generalLinearDeterminantSlice T r m).indicator
        (fun h : Langlands.GeneralLinear (r + 1) F => Φ h.val)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : T2Space F := T.fieldT2
  intro Φ m
  let S : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F) :=
    tsupport (Φ : _ → ℂ) ∩
      {A | T.normalizedAbs (Matrix.det A) = (T.residueCardinality : ℝ) ^ (-m)}
  have hS : IsCompact S :=
    Φ.hasCompactSupport.inter_right
      (isClosed_eq (T.continuous_normalizedAbs.comp continuous_id.matrix_det) continuous_const)
  have hq : (0 : ℝ) < T.residueCardinality :=
    by exact_mod_cast (Nat.zero_lt_one.trans T.residueCardinality_gt_one)
  have hSinv : S ⊆ Set.range
      (Units.val : Langlands.GeneralLinear (r + 1) F →
        Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
    intro A hA
    have hdet : Matrix.det A ≠ 0 := by
      intro hz
      have he := hA.2
      change T.normalizedAbs (Matrix.det A) = _ at he
      rw [hz, T.normalizedAbs_zero] at he
      exact (zpow_pos hq (-m)).ne' he.symm
    have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdet.isUnit
    exact ⟨hunit.unit, hunit.unit_spec⟩
  have hc : IsCompact
      ((Units.val : Langlands.GeneralLinear (r + 1) F →
        Matrix (Fin (r + 1)) (Fin (r + 1)) F) ⁻¹' S) :=
    (isEmbedding_generalLinear_val (r + 1)).isInducing.isCompact_preimage' hS hSinv
  refine HasCompactSupport.intro hc fun h hh => ?_
  by_cases hm : h ∈ generalLinearDeterminantSlice T r m
  · rw [Set.indicator_of_mem hm]
    by_contra hΦ
    exact hh ⟨subset_tsupport _ hΦ,
      normalizedAbs_det_of_mem_generalLinearDeterminantSlice T hm⟩
  · exact Set.indicator_of_notMem hm _

/-- The actual compactly supported group test obtained from a full-matrix test
and a fixed determinant slice. -/
def matrixSliceTest (r : ℕ) :
    letI := T.topology
    GodementJacquet.MatrixTestFunction r F → ℤ →
      SchwartzBruhat (Langlands.GeneralLinear (r + 1) F) := by
  letI := T.topology
  intro Φ m
  refine ⟨(generalLinearDeterminantSlice T r m).indicator (fun h => Φ h.val), ?_,
    hasCompactSupport_matrixSlice T r Φ m⟩
  exact (LocallyConstant.indicator
    ⟨_, Φ.locallyConstant.comp_continuous Units.continuous_val⟩
    (isClopen_generalLinearDeterminantSlice T r m)).isLocallyConstant

@[simp] theorem matrixSliceTest_apply (r : ℕ) :
    letI := T.topology
    ∀ (Φ : GodementJacquet.MatrixTestFunction r F) (m : ℤ)
      (h : Langlands.GeneralLinear (r + 1) F),
      matrixSliceTest T r Φ m h =
        (generalLinearDeterminantSlice T r m).indicator (fun h => Φ h.val) h := by
  let := T.topology
  intro Φ m h
  rfl

end Langlands.AllField.RankinSelberg
