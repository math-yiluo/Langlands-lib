import Langlands.Representation.RankinSelberg.AdjacentRankJointShell
import Langlands.AllField.Group.GL.PadicBlocksSupplement
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankDeterminantShells
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
import Langlands.AllField.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof
/-! Compact joint determinant shells in JPSS Section 6.3, formulas (5) and (11). -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open scoped _root_.Topology

universe uF uV

section Pairing


end Pairing

namespace Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankModelIntegral continuous_adjacentRankJointShellKernel exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankJointShellKernel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankJointShellKernel isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance jointShellFieldT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance jointShellGroupMeasurableSpace (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F) := borel _
local instance jointShellGroupBorelSpace (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance jointShellQuotientMeasurableSpace (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F) := borel _
local instance jointShellQuotientBorelSpace (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F) := ⟨rfl⟩
local instance jointShellQuotientT2 (r : ℕ) : T2Space (LeftUnipotentQuotient r F) :=
  leftQuotient_t2Space _ (GeneralLinear.UpperUnipotent.isClosed (R := F))
local instance jointShellGroupSecondCountable (r : ℕ) : SecondCountableTopology
    (Langlands.GeneralLinear (r + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (r + 1)
local instance jointShellGroupSigmaCompact (r : ℕ) : SigmaCompactSpace
    (Langlands.GeneralLinear (r + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (r + 1)

/-- A square matrix test gives a lower bound for the determinant order wherever
its restriction to the actual general linear group is nonzero. -/
theorem exists_matrixTest_determinantOrder_lowerBound {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F) :
    ∃ L : ℤ, ∀ h : Langlands.GeneralLinear (r + 1) F,
      Φ h.val ≠ 0 →
        L ≤ (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant h : F) := by
  let T := (⟨⟩ : LocalFieldData F)
  have hc : Continuous (fun A : Matrix (Fin (r + 1)) (Fin (r + 1)) F =>
      T.normalizedAbs (Matrix.det A)) := T.continuous_normalizedAbs.comp continuous_id.matrix_det
  obtain ⟨C, hC⟩ := Φ.hasCompactSupport.exists_bound_of_continuousOn hc.continuousOn
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C hq
  refine ⟨-(N : ℤ), fun h hh => ?_⟩
  change -(N : ℤ) ≤ T.ord (GeneralLinear.determinant h : F)
  have hb := hC h.val (subset_tsupport _ hh)
  rw [Real.norm_eq_abs, abs_of_nonneg (T.normalizedAbs_nonneg _)] at hb
  change T.normalizedAbs (GeneralLinear.determinant h : F) ≤ C at hb
  rw [T.normalizedAbs_of_ne_zero (GeneralLinear.determinant h).ne_zero] at hb
  by_contra hn
  have he : (T.residueCardinality : ℝ) ^ (N : ℤ) ≤
      (T.residueCardinality : ℝ) ^
        (-T.ord (GeneralLinear.determinant h : F)) :=
    zpow_le_zpow_right₀ hq.le (by omega)
  rw [zpow_natCast] at he
  linarith

/-- Smooth Whittaker row data likewise has determinant order bounded below.
This is the pointwise support argument, before integration. -/
theorem exists_whittakerRow_determinantOrder_lowerBound {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Fin (r + 1) → F)) :
    ∃ L : ℤ, ∀ g : Langlands.GeneralLinear (r + 1) F,
      W.val.val g ≠ 0 → Φ (lastRow g) ≠ 0 →
        L ≤ (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) := by
  let T := (⟨⟩ : LocalFieldData F)
  obtain ⟨R, hR, hroot⟩ := Langlands.AllField.Whittaker.smoothSimpleRootSupport F T r ψ V σ hσ ℓ W
  obtain ⟨C, hC, hΦ⟩ := exists_schwartzBruhat_row_bound T r Φ
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
    (∏ i : Fin (r + 1), R ^ (r - i.val) * C) hq
  refine ⟨-(N : ℤ), fun g hW hP => ?_⟩
  change -(N : ℤ) ≤ T.ord (GeneralLinear.determinant g : F)
  have hb := normalizedAbs_determinant_le_of_simpleRoot T r ψ W.val hR hC hroot g hW
    (hΦ _ hP)
  rw [T.normalizedAbs_of_ne_zero (GeneralLinear.determinant g).ne_zero] at hb
  by_contra hn
  have he : (T.residueCardinality : ℝ) ^ (N : ℤ) ≤
      (T.residueCardinality : ℝ) ^
        (-T.ord (GeneralLinear.determinant g : F)) :=
    zpow_le_zpow_right₀ hq.le (by omega)
  rw [zpow_natCast] at he
  linarith

/-- The total determinant shell `ord(det g) + ord(det h) = m`. -/
def adjacentRankJointShell (r : ℕ) (m : ℤ) :
    Set (LeftUnipotentQuotient r F ×
      Langlands.GeneralLinear (r + 1) F) :=
  {z | determinantOrder (⟨⟩ : LocalFieldData F) r z.1 +
    (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant z.2 : F) = m}

theorem isClopen_adjacentRankJointShell (r : ℕ) (m : ℤ) :
    IsClopen (adjacentRankJointShell F r m) :=
  (isClopen_discrete ({m} : Set ℤ)).preimage
    (((continuous_determinantOrder (⟨⟩ : LocalFieldData F) r).comp continuous_fst).add
      ((continuous_ord_units (⟨⟩ : LocalFieldData F)).comp
        (((⟨⟩ : LocalFieldData F).generalLinearDeterminant (r + 1)).continuous.comp
          continuous_snd)))

/-- The actual sheared double integrand on a fixed total determinant shell.
The scalar multiplier `a` accommodates all character and norm weights. -/
def adjacentRankJointShellKernel {r : ℕ} (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (a : Langlands.GeneralLinear (r + 1) F → ℂ) (m : ℤ) :
    LeftUnipotentQuotient r F × Langlands.GeneralLinear (r + 1) F → ℂ :=
  (adjacentRankJointShell F r m).indicator (fun z =>
    adjacentRankShiftedPairing ψ W W' z * φ (quotientLastRow r z.1) * Φ z.2.val * a z.2)

@[simp] theorem adjacentRankJointShellKernel_mk {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (a : Langlands.GeneralLinear (r + 1) F → ℂ) (m : ℤ)
    (g h : Langlands.GeneralLinear (r + 1) F) :
    adjacentRankJointShellKernel F ψ W W' Φ φ a m (Quotient.mk _ g, h) =
      if (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) +
          (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant h : F) = m
      then W.val g * W'.val (g * h) * φ (lastRow g) * Φ h.val * a h else 0 := by
  classical
  simp [adjacentRankJointShellKernel, adjacentRankJointShell, Set.indicator_apply]

theorem continuous_adjacentRankJointShellKernel {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (hW : Continuous W.val) (hW' : Continuous W'.val)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (a : Langlands.GeneralLinear (r + 1) F → ℂ) (ha : Continuous a) (m : ℤ) :
    Continuous (adjacentRankJointShellKernel F ψ W W' Φ φ a m) := by
  have hrow : Continuous (quotientLastRow (F := F) r) := by
    apply Continuous.quotient_lift
    exact continuous_lastRow
  apply (isClopen_adjacentRankJointShell F r m).continuous_indicator
  exact ((((continuous_adjacentRankShiftedPairing ψ W W' hW hW').mul
    (φ.continuous.comp (hrow.comp continuous_fst))).mul
      (Φ.continuous.comp (Units.continuous_val.comp continuous_snd))).mul
        (ha.comp continuous_snd))

/-- Each total determinant shell has compact joint support. Only smoothness of
the first representation is needed; no growth hypothesis on the second function
or scalar multiplier enters this support argument. -/
theorem hasCompactSupport_adjacentRankJointShellKernel {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (a : Langlands.GeneralLinear (r + 1) F → ℂ) (m : ℤ) :
    HasCompactSupport (adjacentRankJointShellKernel F ψ W.val W' Φ φ a m) := by
  classical
  let T := (⟨⟩ : LocalFieldData F)
  obtain ⟨Lq, hLq⟩ := exists_whittakerRow_determinantOrder_lowerBound F ψ σ hσ ℓ W φ
  obtain ⟨Lh, hLh⟩ := exists_matrixTest_determinantOrder_lowerBound F Φ
  let Q : Set (LeftUnipotentQuotient r F) :=
    ⋃ j ∈ Finset.Icc Lq (m - Lh),
      tsupport ((determinantSlice T r j).indicator
        (fun q => whittakerNorm ψ W.val q * ‖φ (quotientLastRow r q)‖))
  let H : Set (Langlands.GeneralLinear (r + 1) F) :=
    ⋃ j ∈ Finset.Icc Lh (m - Lq), tsupport (matrixSliceTest T r Φ j)
  have hQ : IsCompact Q :=
    (Finset.Icc Lq (m - Lh)).isCompact_biUnion fun j _ =>
      (whittakerRowSliceCompactSupport F T r ψ V σ hσ ℓ W φ j).isCompact
  have hH : IsCompact H :=
    (Finset.Icc Lh (m - Lq)).isCompact_biUnion fun j _ =>
      (matrixSliceTest T r Φ j).hasCompactSupport
  refine HasCompactSupport.intro (hQ.prod hH) ?_
  rintro ⟨q, h⟩ hnot
  induction q using Quotient.inductionOn with
  | h g =>
    by_contra hne
    rw [adjacentRankJointShellKernel_mk] at hne
    split_ifs at hne with hm
    · have hW : W.val.val g ≠ 0 := fun hz => hne (by rw [hz, zero_mul, zero_mul, zero_mul, zero_mul])
      have hφ : φ (lastRow g) ≠ 0 := fun hz => hne (by rw [hz, mul_zero, zero_mul, zero_mul])
      have hΦ : Φ h.val ≠ 0 := fun hz => hne (by rw [hz, mul_zero, zero_mul])
      have hqbound := hLq g hW hφ
      have hhbound := hLh h hΦ
      change Lq ≤ T.ord (GeneralLinear.determinant g : F) at hqbound
      change Lh ≤ T.ord (GeneralLinear.determinant h : F) at hhbound
      change T.ord (GeneralLinear.determinant g : F) +
        T.ord (GeneralLinear.determinant h : F) = m at hm
      apply hnot
      constructor
      · refine Set.mem_iUnion.mpr ⟨T.ord (GeneralLinear.determinant g : F),
          Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hqbound, by omega⟩, ?_⟩⟩
        apply subset_tsupport
        change (determinantSlice T r (T.ord (GeneralLinear.determinant g : F))).indicator
          (fun q => whittakerNorm ψ W.val q * ‖φ (quotientLastRow r q)‖)
            (Quotient.mk _ g) ≠ 0
        rw [Set.indicator_of_mem (show (Quotient.mk _ g : LeftUnipotentQuotient r F) ∈
          determinantSlice T r (T.ord (GeneralLinear.determinant g : F)) from rfl)]
        exact mul_ne_zero (norm_ne_zero_iff.mpr hW) (norm_ne_zero_iff.mpr hφ)
      · refine Set.mem_iUnion.mpr ⟨T.ord (GeneralLinear.determinant h : F),
          Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hhbound, by omega⟩, ?_⟩⟩
        apply subset_tsupport
        change matrixSliceTest T r Φ (T.ord (GeneralLinear.determinant h : F)) h ≠ 0
        rw [matrixSliceTest_apply, Set.indicator_of_mem
          (show h ∈ generalLinearDeterminantSlice T r
            (T.ord (GeneralLinear.determinant h : F)) from rfl)]
        exact hΦ
    · exact hne rfl

/-- Absolute joint convergence of the fixed-shell double integral for any
Borel measures finite on compact sets. -/
theorem integrable_adjacentRankJointShellKernel {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r) (hW' : Continuous W'.val)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (a : Langlands.GeneralLinear (r + 1) F → ℂ) (ha : Continuous a) (m : ℤ)
    (μ : Measure (LeftUnipotentQuotient r F)) [IsFiniteMeasureOnCompacts μ]
    (η : Measure (Langlands.GeneralLinear (r + 1) F))
    [IsFiniteMeasureOnCompacts η] :
    Integrable (adjacentRankJointShellKernel F ψ W.val W' Φ φ a m) (μ.prod η) :=
  (continuous_adjacentRankJointShellKernel F ψ W.val W'
    (glModelFunction_continuous ψ r σ hσ ℓ W) hW' Φ φ a ha m).integrable_of_hasCompactSupport
      (hasCompactSupport_adjacentRankJointShellKernel F ψ σ hσ ℓ W W' Φ φ a m)

end Padic
end Langlands.AllField.RankinSelberg
