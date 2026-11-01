import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.Representation.GodementJacquet.Zeta
import Langlands.LocalField.Normalization.Continuity

/-! Compact inner determinant slices for the calculation of JPSS Section 6.3. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The actual general-linear determinant slice, before taking a unipotent quotient. -/
def generalLinearDeterminantSlice (r : ℕ) (m : ℤ) :
    Set (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  {h | T.ord (GeneralLinear.determinant h : F.Carrier) = m}

@[simp] theorem mem_generalLinearDeterminantSlice {r : ℕ} {m : ℤ}
    {h : Langlands.GeneralLinear (r + 1) F.Carrier} :
    h ∈ generalLinearDeterminantSlice T r m ↔
      T.ord (GeneralLinear.determinant h : F.Carrier) = m := Iff.rfl

/-- The group slice is exactly the inverse image of the published quotient slice. -/
theorem generalLinearDeterminantSlice_eq_preimage (r : ℕ) (m : ℤ) :
    generalLinearDeterminantSlice T r m =
      (fun h : Langlands.GeneralLinear (r + 1) F.Carrier =>
        (Quotient.mk _ h : LeftUnipotentQuotient r F.Carrier)) ⁻¹'
          determinantSlice T r m := rfl

theorem isClopen_generalLinearDeterminantSlice (r : ℕ) (m : ℤ) :
    letI := T.topology
    IsClopen (generalLinearDeterminantSlice T r m) := by
  let := T.topology
  exact (isClopen_discrete ({m} : Set ℤ)).preimage
    ((continuous_ord_units T).comp (T.generalLinearDeterminant (r + 1)).continuous)

/-- On the group slice, normalized determinant absolute value has the required
strictly positive constant value. -/
theorem normalizedAbs_det_of_mem_generalLinearDeterminantSlice {r : ℕ} {m : ℤ}
    {h : Langlands.GeneralLinear (r + 1) F.Carrier}
    (hh : h ∈ generalLinearDeterminantSlice T r m) :
    T.normalizedAbs (Matrix.det h.val) = (T.residueCardinality : ℝ) ^ (-m) := by
  change T.normalizedAbs (GeneralLinear.determinant h : F.Carrier) = _
  rw [T.normalizedAbs_of_ne_zero (GeneralLinear.determinant h).ne_zero, hh]

/-- A compact full-matrix test, cut out by a fixed determinant slice, has compact
support on the actual general linear group. No bound on a coefficient is needed. -/
theorem hasCompactSupport_matrixSlice (r : ℕ) :
    letI := T.topology
    ∀ (Φ : GodementJacquet.MatrixTestFunction r F.Carrier) (m : ℤ),
      HasCompactSupport ((generalLinearDeterminantSlice T r m).indicator
        (fun h : Langlands.GeneralLinear (r + 1) F.Carrier => Φ h.val)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : T2Space F.Carrier := T.fieldT2
  intro Φ m
  let S : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) :=
    tsupport (Φ : _ → ℂ) ∩
      {A | T.normalizedAbs (Matrix.det A) = (T.residueCardinality : ℝ) ^ (-m)}
  have hS : IsCompact S :=
    Φ.hasCompactSupport.inter_right
      (isClosed_eq (T.continuous_normalizedAbs.comp continuous_id.matrix_det) continuous_const)
  have hq : (0 : ℝ) < T.residueCardinality :=
    by exact_mod_cast (Nat.zero_lt_one.trans T.residueCardinality_gt_one)
  have hSinv : S ⊆ Set.range
      (Units.val : Langlands.GeneralLinear (r + 1) F.Carrier →
        Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) := by
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
      ((Units.val : Langlands.GeneralLinear (r + 1) F.Carrier →
        Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) ⁻¹' S) :=
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
    GodementJacquet.MatrixTestFunction r F.Carrier → ℤ →
      SchwartzBruhat (Langlands.GeneralLinear (r + 1) F.Carrier) := by
  letI := T.topology
  intro Φ m
  refine ⟨(generalLinearDeterminantSlice T r m).indicator (fun h => Φ h.val), ?_,
    hasCompactSupport_matrixSlice T r Φ m⟩
  exact (LocallyConstant.indicator
    ⟨_, Φ.locallyConstant.comp_continuous Units.continuous_val⟩
    (isClopen_generalLinearDeterminantSlice T r m)).isLocallyConstant

@[simp] theorem matrixSliceTest_apply (r : ℕ) :
    letI := T.topology
    ∀ (Φ : GodementJacquet.MatrixTestFunction r F.Carrier) (m : ℤ)
      (h : Langlands.GeneralLinear (r + 1) F.Carrier),
      matrixSliceTest T r Φ m h =
        (generalLinearDeterminantSlice T r m).indicator (fun h => Φ h.val) h := by
  let := T.topology
  intro Φ m h
  rfl

/-- Every continuous coefficient times a matrix test is integrable on each
fixed group determinant slice, for every measure finite on compact sets. -/
theorem integrableOn_matrixSlice_mul (r : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier)]
      [BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier)]
      (μ : Measure (Langlands.GeneralLinear (r + 1) F.Carrier))
      [IsFiniteMeasureOnCompacts μ]
      (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
      (f : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ),
      Continuous f → ∀ m : ℤ,
        IntegrableOn (fun h => Φ h.val * f h) (generalLinearDeterminantSlice T r m) μ := by
  let := T.topology
  intro _ _ μ _ Φ f hf m
  have hs := isClopen_generalLinearDeterminantSlice T r m
  rw [← integrable_indicator_iff hs.isOpen.measurableSet]
  have he : (generalLinearDeterminantSlice T r m).indicator (fun h => Φ h.val * f h) =
      fun h => matrixSliceTest T r Φ m h * f h := by
    funext h
    simp only [matrixSliceTest_apply, Set.indicator_mul_left]
  rw [he]
  exact ((matrixSliceTest T r Φ m).continuous.mul hf).integrable_of_hasCompactSupport
    (matrixSliceTest T r Φ m).hasCompactSupport.mul_right

end Langlands.RankinSelberg
