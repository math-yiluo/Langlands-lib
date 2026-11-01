import Langlands.Representation.RankinSelberg.AdjacentRankDeterminantShells
import Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof
import Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
import Langlands.Group.GL.CountabilityProof
import Mathlib.MeasureTheory.Integral.Prod

/-! Compact joint determinant shells in JPSS Section 6.3, formulas (5) and (11). -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration
open scoped Topology

universe uF uV

section Pairing

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
  (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)

/-- The genuine product `W(g) W'(g h)`, descended in the first variable. -/
def adjacentRankShiftedPairing (z : LeftUnipotentQuotient r F ×
    Langlands.GeneralLinear (r + 1) F) : ℂ :=
  descend _ (fun g => W.val g * W'.val (g * z.2)) (by
    intro u g
    rw [mul_assoc, W.property u g, W'.property u (g * z.2)]
    change ((standardCharacter ψ r u : ℂ) * W.val g) *
        ((((standardCharacter ψ r u)⁻¹ : ℂˣ) : ℂ) * W'.val (g * z.2)) = _
    rw [mul_mul_mul_comm, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]) z.1

@[simp] theorem adjacentRankShiftedPairing_mk
    (g h : Langlands.GeneralLinear (r + 1) F) :
    adjacentRankShiftedPairing ψ W W' (Quotient.mk _ g, h) =
      W.val g * W'.val (g * h) := rfl

/-- Continuity descends jointly through the open quotient map times the identity. -/
theorem continuous_adjacentRankShiftedPairing [IsTopologicalRing F]
    (hW : Continuous W.val) (hW' : Continuous W'.val) :
    Continuous (adjacentRankShiftedPairing ψ W W') := by
  let G := Langlands.GeneralLinear (r + 1) F
  have hid : IsOpenQuotientMap (id : G → G) := IsOpenQuotientMap.id
  apply ((leftQuotient_isOpenQuotientMap
    (GeneralLinear.upperUnipotent (r + 1) F)).prodMap hid).isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : G × G => W.val z.1 * W'.val (z.1 * z.2))
  exact (hW.comp continuous_fst).mul (hW'.comp (continuous_fst.mul continuous_snd))

end Pairing

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance jointShellFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance jointShellValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance jointShellLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance jointShellFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance jointShellGroupMeasurableSpace (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance jointShellGroupBorelSpace (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance jointShellQuotientMeasurableSpace (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance jointShellQuotientBorelSpace (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩
local instance jointShellQuotientT2 (r : ℕ) : T2Space (LeftUnipotentQuotient r F.Carrier) :=
  leftQuotient_t2Space _ (GeneralLinear.UpperUnipotent.isClosed (R := F.Carrier))
local instance jointShellGroupSecondCountable (r : ℕ) : SecondCountableTopology
    (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (r + 1)
local instance jointShellGroupSigmaCompact (r : ℕ) : SigmaCompactSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (r + 1)
local instance jointShellQuotientSecondCountable (r : ℕ) : SecondCountableTopology
    (LeftUnipotentQuotient r F.Carrier) :=
  TopologicalSpace.Quotient.secondCountableTopology
    (leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) F.Carrier)).isOpenMap

/-- A square matrix test gives a lower bound for the determinant order wherever
its restriction to the actual general linear group is nonzero. -/
theorem exists_matrixTest_determinantOrder_lowerBound {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier) :
    ∃ L : ℤ, ∀ h : Langlands.GeneralLinear (r + 1) F.Carrier,
      Φ h.val ≠ 0 →
        L ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant h : F.Carrier) := by
  let T := F.canonicalTopologicalData
  have hc : Continuous (fun A : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier =>
      T.normalizedAbs (Matrix.det A)) := T.continuous_normalizedAbs.comp continuous_id.matrix_det
  obtain ⟨C, hC⟩ := Φ.hasCompactSupport.exists_bound_of_continuousOn hc.continuousOn
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C hq
  refine ⟨-(N : ℤ), fun h hh => ?_⟩
  change -(N : ℤ) ≤ T.ord (GeneralLinear.determinant h : F.Carrier)
  have hb := hC h.val (subset_tsupport _ hh)
  rw [Real.norm_eq_abs, abs_of_nonneg (T.normalizedAbs_nonneg _)] at hb
  change T.normalizedAbs (GeneralLinear.determinant h : F.Carrier) ≤ C at hb
  rw [T.normalizedAbs_of_ne_zero (GeneralLinear.determinant h).ne_zero] at hb
  by_contra hn
  have he : (T.residueCardinality : ℝ) ^ (N : ℤ) ≤
      (T.residueCardinality : ℝ) ^
        (-T.ord (GeneralLinear.determinant h : F.Carrier)) :=
    zpow_le_zpow_right₀ hq.le (by omega)
  rw [zpow_natCast] at he
  linarith

/-- Smooth Whittaker row data likewise has determinant order bounded below.
This is the pointwise support argument, before integration. -/
theorem exists_whittakerRow_determinantOrder_lowerBound {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Fin (r + 1) → F.Carrier)) :
    ∃ L : ℤ, ∀ g : Langlands.GeneralLinear (r + 1) F.Carrier,
      W.val.val g ≠ 0 → Φ (lastRow g) ≠ 0 →
        L ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) := by
  let T := F.canonicalTopologicalData
  obtain ⟨R, hR, hroot⟩ := Whittaker.smoothSimpleRootSupport F T r ψ V σ hσ ℓ W
  obtain ⟨C, hC, hΦ⟩ := exists_schwartzBruhat_row_bound T r Φ
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
    (∏ i : Fin (r + 1), R ^ (r - i.val) * C) hq
  refine ⟨-(N : ℤ), fun g hW hP => ?_⟩
  change -(N : ℤ) ≤ T.ord (GeneralLinear.determinant g : F.Carrier)
  have hb := normalizedAbs_determinant_le_of_simpleRoot T r ψ W.val hR hC hroot g hW
    (hΦ _ hP)
  rw [T.normalizedAbs_of_ne_zero (GeneralLinear.determinant g).ne_zero] at hb
  by_contra hn
  have he : (T.residueCardinality : ℝ) ^ (N : ℤ) ≤
      (T.residueCardinality : ℝ) ^
        (-T.ord (GeneralLinear.determinant g : F.Carrier)) :=
    zpow_le_zpow_right₀ hq.le (by omega)
  rw [zpow_natCast] at he
  linarith

/-- The total determinant shell `ord(det g) + ord(det h) = m`. -/
def adjacentRankJointShell (r : ℕ) (m : ℤ) :
    Set (LeftUnipotentQuotient r F.Carrier ×
      Langlands.GeneralLinear (r + 1) F.Carrier) :=
  {z | determinantOrder F.canonicalTopologicalData r z.1 +
    F.canonicalTopologicalData.ord (GeneralLinear.determinant z.2 : F.Carrier) = m}

theorem isClopen_adjacentRankJointShell (r : ℕ) (m : ℤ) :
    IsClopen (adjacentRankJointShell F r m) :=
  (isClopen_discrete ({m} : Set ℤ)).preimage
    (((continuous_determinantOrder F.canonicalTopologicalData r).comp continuous_fst).add
      ((continuous_ord_units F.canonicalTopologicalData).comp
        ((F.canonicalTopologicalData.generalLinearDeterminant (r + 1)).continuous.comp
          continuous_snd)))

/-- The actual sheared double integrand on a fixed total determinant shell.
The scalar multiplier `a` accommodates all character and norm weights. -/
def adjacentRankJointShellKernel {r : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (a : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (m : ℤ) :
    LeftUnipotentQuotient r F.Carrier × Langlands.GeneralLinear (r + 1) F.Carrier → ℂ :=
  (adjacentRankJointShell F r m).indicator (fun z =>
    adjacentRankShiftedPairing ψ W W' z * φ (quotientLastRow r z.1) * Φ z.2.val * a z.2)

@[simp] theorem adjacentRankJointShellKernel_mk {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (a : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (m : ℤ)
    (g h : Langlands.GeneralLinear (r + 1) F.Carrier) :
    adjacentRankJointShellKernel F ψ W W' Φ φ a m (Quotient.mk _ g, h) =
      if F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) +
          F.canonicalTopologicalData.ord (GeneralLinear.determinant h : F.Carrier) = m
      then W.val g * W'.val (g * h) * φ (lastRow g) * Φ h.val * a h else 0 := by
  classical
  simp [adjacentRankJointShellKernel, adjacentRankJointShell, Set.indicator_apply]

theorem continuous_adjacentRankJointShellKernel {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (hW : Continuous W.val) (hW' : Continuous W'.val)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (a : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (ha : Continuous a) (m : ℤ) :
    Continuous (adjacentRankJointShellKernel F ψ W W' Φ φ a m) := by
  have hrow : Continuous (quotientLastRow (F := F.Carrier) r) := by
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
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (a : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (m : ℤ) :
    HasCompactSupport (adjacentRankJointShellKernel F ψ W.val W' Φ φ a m) := by
  classical
  let T := F.canonicalTopologicalData
  obtain ⟨Lq, hLq⟩ := exists_whittakerRow_determinantOrder_lowerBound F ψ σ hσ ℓ W φ
  obtain ⟨Lh, hLh⟩ := exists_matrixTest_determinantOrder_lowerBound F Φ
  let Q : Set (LeftUnipotentQuotient r F.Carrier) :=
    ⋃ j ∈ Finset.Icc Lq (m - Lh),
      tsupport ((determinantSlice T r j).indicator
        (fun q => whittakerNorm ψ W.val q * ‖φ (quotientLastRow r q)‖))
  let H : Set (Langlands.GeneralLinear (r + 1) F.Carrier) :=
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
      change Lq ≤ T.ord (GeneralLinear.determinant g : F.Carrier) at hqbound
      change Lh ≤ T.ord (GeneralLinear.determinant h : F.Carrier) at hhbound
      change T.ord (GeneralLinear.determinant g : F.Carrier) +
        T.ord (GeneralLinear.determinant h : F.Carrier) = m at hm
      apply hnot
      constructor
      · refine Set.mem_iUnion.mpr ⟨T.ord (GeneralLinear.determinant g : F.Carrier),
          Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hqbound, by omega⟩, ?_⟩⟩
        apply subset_tsupport
        change (determinantSlice T r (T.ord (GeneralLinear.determinant g : F.Carrier))).indicator
          (fun q => whittakerNorm ψ W.val q * ‖φ (quotientLastRow r q)‖)
            (Quotient.mk _ g) ≠ 0
        rw [Set.indicator_of_mem (show (Quotient.mk _ g : LeftUnipotentQuotient r F.Carrier) ∈
          determinantSlice T r (T.ord (GeneralLinear.determinant g : F.Carrier)) from rfl)]
        exact mul_ne_zero (norm_ne_zero_iff.mpr hW) (norm_ne_zero_iff.mpr hφ)
      · refine Set.mem_iUnion.mpr ⟨T.ord (GeneralLinear.determinant h : F.Carrier),
          Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hhbound, by omega⟩, ?_⟩⟩
        apply subset_tsupport
        change matrixSliceTest T r Φ (T.ord (GeneralLinear.determinant h : F.Carrier)) h ≠ 0
        rw [matrixSliceTest_apply, Set.indicator_of_mem
          (show h ∈ generalLinearDeterminantSlice T r
            (T.ord (GeneralLinear.determinant h : F.Carrier)) from rfl)]
        exact hΦ
    · exact hne rfl

/-- Absolute joint convergence of the fixed-shell double integral for any
Borel measures finite on compact sets. -/
theorem integrable_adjacentRankJointShellKernel {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r) (hW' : Continuous W'.val)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (a : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (ha : Continuous a) (m : ℤ)
    (μ : Measure (LeftUnipotentQuotient r F.Carrier)) [IsFiniteMeasureOnCompacts μ]
    (η : Measure (Langlands.GeneralLinear (r + 1) F.Carrier))
    [IsFiniteMeasureOnCompacts η] :
    Integrable (adjacentRankJointShellKernel F ψ W.val W' Φ φ a m) (μ.prod η) :=
  (continuous_adjacentRankJointShellKernel F ψ W.val W'
    (glModelFunction_continuous ψ r σ hσ ℓ W) hW' Φ φ a ha m).integrable_of_hasCompactSupport
      (hasCompactSupport_adjacentRankJointShellKernel F ψ σ hσ ℓ W W' Φ φ a m)

end Padic
end Langlands.RankinSelberg
