import Langlands.Representation.RankinSelberg.AdjacentRankQuotientShear
import Langlands.Representation.RankinSelberg.AdjacentRankInnerSliceSeparation
import Langlands.Representation.RankinSelberg.InducedTailIntermediateCoefficientAdapters

/-! The finite determinant-shell convolution in JPSS Section 6.3, (8)--(10). -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration
open scoped BigOperators Topology

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance shellConvolutionFieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance shellConvolutionValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance shellConvolutionLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance shellConvolutionFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance shellConvolutionGroupMeasurable (r : ℕ) : MeasurableSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance shellConvolutionGroupBorel (r : ℕ) : BorelSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance shellConvolutionUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := borel _
local instance shellConvolutionUnipotentBorel (r : ℕ) : BorelSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance shellConvolutionQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance shellConvolutionQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩
local instance shellConvolutionQuotientT2 (r : ℕ) : T2Space (LeftUnipotentQuotient r F.Carrier) :=
  leftQuotient_t2Space _ (GeneralLinear.UpperUnipotent.isClosed (R := F.Carrier))
local instance shellConvolutionGroupSecondCountable (r : ℕ) : SecondCountableTopology
    (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (r + 1)
local instance shellConvolutionGroupSigmaCompact (r : ℕ) : SigmaCompactSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (r + 1)
local instance shellConvolutionQuotientSecondCountable (r : ℕ) : SecondCountableTopology
    (LeftUnipotentQuotient r F.Carrier) :=
  TopologicalSpace.Quotient.secondCountableTopology
    (leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) F.Carrier)).isOpenMap
local instance shellConvolutionQuotientLocallyCompact (r : ℕ) : LocallyCompactSpace
    (LeftUnipotentQuotient r F.Carrier) :=
  leftQuotient_locallyCompactSpace _

/-- The actual continuous character and norm multiplier in the inner integral. -/
def adjacentRankInnerMultiplier {r : ℕ} (χ : Quasicharacter F.Carrier) (s : ℂ)
    (h : Langlands.GeneralLinear (r + 1) F.Carrier) : ℂ :=
  (χ (GeneralLinear.determinant h) : ℂ) *
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h s

theorem continuous_adjacentRankInnerMultiplier {r : ℕ}
    (χ : Quasicharacter F.Carrier) (s : ℂ) :
    Continuous (adjacentRankInnerMultiplier F (r := r) χ s) :=
  (Units.continuous_val.comp (χ.continuous.comp
    (F.canonicalTopologicalData.generalLinearDeterminant (r + 1)).continuous)).mul
      (continuous_adjacentRank_determinantWeight F (r + 1) s)

/-- The equal-rank integrand at zero has compact support on every quotient
slice when its first member is an actual smooth coefficient-image vector. -/
theorem hasCompactSupport_equalRankSlice {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier)) (k : ℤ) :
    HasCompactSupport ((determinantSlice F.canonicalTopologicalData r k).indicator
      (equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        W.val W' φ 0)) := by
  have hc := whittakerRowSliceCompactSupport F F.canonicalTopologicalData r ψ V σ hσ ℓ W φ k
  apply hc.mono
  intro q hq
  rw [Function.mem_support, Set.indicator_apply_ne_zero] at hq ⊢
  refine ⟨hq.1, ?_⟩
  induction q using Quotient.inductionOn with
  | h g =>
    have hv : equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        W.val W' φ 0 (Quotient.mk _ g) ≠ 0 := hq.2
    rw [equalRankIntegrand_zero_mk] at hv
    change ‖W.val.val g‖ * ‖φ (lastRow g)‖ ≠ 0
    exact mul_ne_zero (norm_ne_zero_iff.mpr (mul_ne_zero_iff.mp
      (mul_ne_zero_iff.mp hv).1).1)
      (norm_ne_zero_iff.mpr (mul_ne_zero_iff.mp hv).2)

/-- In particular every such equal-rank slice is genuinely integrable against
any Borel quotient measure finite on compact sets. -/
theorem integrable_equalRankSlice {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r) (hW' : Continuous W'.val)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier)) (k : ℤ)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier)) [IsFiniteMeasureOnCompacts ν] :
    Integrable ((determinantSlice F.canonicalTopologicalData r k).indicator
      (equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        W.val W' φ 0)) ν := by
  have hcont : Continuous (equalRankIntegrand ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) W.val W' φ 0) := by
    apply (leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) F.Carrier)).isQuotientMap.continuous_iff.mpr
    change Continuous (fun g => W.val.val g * W'.val g * φ (lastRow g) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g 0)
    simp only [determinantWeight_zero, mul_one]
    exact Continuous.mul
      (f := fun g => W.val.val g * W'.val g)
      (g := fun g => φ (lastRow g))
      ((glModelFunction_continuous ψ r σ hσ ℓ W).mul hW')
      (φ.continuous.comp continuous_lastRow)
  exact ((isClopen_determinantSlice F.canonicalTopologicalData r k).continuous_indicator
    hcont).integrable_of_hasCompactSupport
      (hasCompactSupport_equalRankSlice F ψ σ hσ ℓ W W' φ k)

/-- A finite support bound in determinant order gives an exact finite partition
of the integral. The bound concerns actual pointwise support. -/
theorem integral_eq_sum_determinantSlices {r : ℕ}
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (f : LeftUnipotentQuotient r F.Carrier → ℂ) (hf : Integrable f ν)
    (I : Finset ℤ)
    (hI : ∀ q, f q ≠ 0 → determinantOrder F.canonicalTopologicalData r q ∈ I) :
    (∫ q, f q ∂ν) = ∑ k ∈ I,
      ∫ q, (determinantSlice F.canonicalTopologicalData r k).indicator f q ∂ν := by
  classical
  have heq : f = fun q => ∑ k ∈ I,
      (determinantSlice F.canonicalTopologicalData r k).indicator f q := by
    funext q
    by_cases hz : f q = 0
    · simp [Set.indicator_apply, hz]
    · symm
      rw [Finset.sum_eq_single (determinantOrder F.canonicalTopologicalData r q)]
      · exact Set.indicator_of_mem (show q ∈ determinantSlice
          F.canonicalTopologicalData r (determinantOrder F.canonicalTopologicalData r q)
          from rfl) _
      · intro k hk hne
        exact Set.indicator_of_notMem (fun he => hne he.symm) _
      · exact fun hn => (hn (hI q hz)).elim
  calc
    _ = ∫ q, ∑ k ∈ I, (determinantSlice F.canonicalTopologicalData r k).indicator f q ∂ν :=
      congrArg (fun g => ∫ q, g q ∂ν) heq
    _ = _ := integral_finsetSum I fun k _ =>
      hf.indicator (measurableSet_determinantSlice F.canonicalTopologicalData r k)

/-- On a fixed quotient slice, the joint cutoff is precisely the complementary
group slice. This is the pointwise identity underlying the convolution. -/
theorem adjacentRankJointShellKernel_mk_eq_innerSlice {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier) (m k : ℤ) (s : ℂ)
    (g h : Langlands.GeneralLinear (r + 1) F.Carrier)
    (hg : F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = k) :
    adjacentRankJointShellKernel F ψ W W' Φ φ
        (adjacentRankInnerMultiplier F χ s) m (Quotient.mk _ g, h) =
      W.val g * φ (lastRow g) *
        (adjacentRankInnerSliceWeight F Φ χ (m - k) s h * W'.val (g * h)) := by
  rw [adjacentRankJointShellKernel_mk]
  simp only [adjacentRankInnerSliceWeight, matrixSliceTest_apply,
    adjacentRankInnerMultiplier]
  by_cases hh : F.canonicalTopologicalData.ord
      (GeneralLinear.determinant h : F.Carrier) = m - k
  · have hs : F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) +
        F.canonicalTopologicalData.ord (GeneralLinear.determinant h : F.Carrier) = m := by
      omega
    rw [ite_eq_left hs, Set.indicator_of_mem (show h ∈
      generalLinearDeterminantSlice F.canonicalTopologicalData r (m - k) from hh)]
    ring
  · have hs : F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) +
        F.canonicalTopologicalData.ord (GeneralLinear.determinant h : F.Carrier) ≠ m := by
      omega
    rw [ite_eq_right hs, Set.indicator_of_notMem (show h ∉
      generalLinearDeterminantSlice F.canonicalTopologicalData r (m - k) from hh)]
    simp only [zero_mul, mul_zero]

set_option maxHeartbeats 1600000 in
/-- The actual fixed-shell coefficient calculation. The finite basis is chosen
before the second vector, and its matrix coefficients before all shell orders
and exponents. Both product integrals and all factors are genuinely integrable. -/
theorem adjacentRankShell_finiteConvolution {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsAdmissible τ) (ℓ' : glFunctionals (ψ.scale (-1)) r τ)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (GeneralLinear.upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν) :
    ∃ (Lq Lh : ℤ) (N : ℕ)
      (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      (∀ g, W.val.val g ≠ 0 → φ (lastRow g) ≠ 0 →
        Lq ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier)) ∧
      (∀ h : Langlands.GeneralLinear (r + 1) F.Carrier, Φ h.val ≠ 0 →
        Lh ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant h : F.Carrier)) ∧
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'),
          ∀ (m : ℤ) (s : ℂ),
            let Winv := InducedTailIntermediate.scaledStandardAsInverse ψ W'.val
            let Binv := fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val
            let a := adjacentRankInnerMultiplier F χ s
            let η := generalLinearHaar F.Carrier r
            let after := adjacentRankJointShellKernel F ψ W.val Winv Φ φ a m
            let before := adjacentRankBeforeShearKernel F ψ W.val Winv Φ φ a m
            let rhs := ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
              equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W.val (Binv i) φ k *
                ∫ h, adjacentRankInnerSliceWeight F Φ χ (m - k) s h * (f i).val h ∂η
            Integrable before (ν.prod η) ∧ Integrable after (ν.prod η) ∧
              (∀ k i, Integrable ((determinantSlice F.canonicalTopologicalData r k).indicator
                (equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
                  W.val (Binv i) φ 0)) ν) ∧
              (∀ j i, Integrable (fun h =>
                adjacentRankInnerSliceWeight F Φ χ j s h * (f i).val h) η) ∧
              (∫ z, after z ∂ν.prod η) = rhs ∧
              (∫ q, ∫ h, before (q, h) ∂η ∂ν) = rhs := by
  classical
  let := hν.regular
  obtain ⟨Lq, hLq⟩ := exists_whittakerRow_determinantOrder_lowerBound F ψ σ hσ ℓ W φ
  obtain ⟨Lh, hLh⟩ := exists_matrixTest_determinantOrder_lowerBound F Φ
  obtain ⟨N, B, hB⟩ := adjacentRankInnerSlice_finiteSeparation F (ψ.scale (-1)) τ hτ ℓ' Φ χ
  refine ⟨Lq, Lh, N, B, hLq, hLh, fun W' => ?_⟩
  obtain ⟨f, hf⟩ := hB W'
  refine ⟨f, fun m s => ?_⟩
  dsimp only
  let Winv := InducedTailIntermediate.scaledStandardAsInverse ψ W'.val
  let Binv := fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val
  let η := generalLinearHaar F.Carrier r
  let a := adjacentRankInnerMultiplier F (r := r) χ s
  let after := adjacentRankJointShellKernel F ψ W.val Winv Φ φ a m
  let before := adjacentRankBeforeShearKernel F ψ W.val Winv Φ φ a m
  let outer := fun q => ∫ h, after (q, h) ∂η
  let I := Finset.Icc Lq (m - Lh)
  have hW' : Continuous Winv.val := glModelFunction_continuous (ψ.scale (-1)) r τ hτ.1 ℓ' W'
  obtain ⟨hb, ha, -, ho, -, hba, -⟩ :=
    adjacentRankShell_shear_fubini F ψ σ hσ ℓ W Winv hW' Φ φ a
      (continuous_adjacentRankInnerMultiplier F χ s) m ν hν
  have hBi (i : Fin N) : Continuous (Binv i).val :=
    glModelFunction_continuous (ψ.scale (-1)) r τ hτ.1 ℓ' (B i)
  have hslice (k : ℤ) (i : Fin N) :
      Integrable ((determinantSlice F.canonicalTopologicalData r k).indicator
        (equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          W.val (Binv i) φ 0)) ν :=
    integrable_equalRankSlice F ψ σ hσ ℓ W (Binv i) (hBi i) φ k ν
  have hfi (j : ℤ) (i : Fin N) : Integrable (fun h =>
      adjacentRankInnerSliceWeight F Φ χ j s h * (f i).val h) η :=
    (hf j s 1).2.1 i
  have hsupport (q : LeftUnipotentQuotient r F.Carrier)
      (h : Langlands.GeneralLinear (r + 1) F.Carrier) (hz : after (q, h) ≠ 0) :
      determinantOrder F.canonicalTopologicalData r q ∈ I := by
    induction q using Quotient.inductionOn with
    | h g =>
      change adjacentRankJointShellKernel F ψ W.val Winv Φ φ a m
        (Quotient.mk _ g, h) ≠ 0 at hz
      rw [adjacentRankJointShellKernel_mk] at hz
      split_ifs at hz with hs
      · have htest := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).2
        have hrow := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp
          (mul_ne_zero_iff.mp hz).1).1).2
        have hfirst := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp
          (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).1).1).1
        have hq := hLq g hfirst hrow
        have hh := hLh h htest
        exact Finset.mem_Icc.mpr ⟨hq, by
          change F.canonicalTopologicalData.ord
            (GeneralLinear.determinant g : F.Carrier) ≤ m - Lh
          omega⟩
      · exact (hz rfl).elim
  have houterSupport (q : LeftUnipotentQuotient r F.Carrier) (hz : outer q ≠ 0) :
      determinantOrder F.canonicalTopologicalData r q ∈ I := by
    by_contra hn
    apply hz
    exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun h =>
      by_contra fun hh => hn (hsupport q h hh))
  have hpoint (k : ℤ) :
      (determinantSlice F.canonicalTopologicalData r k).indicator outer =
        fun q => ∑ i, (determinantSlice F.canonicalTopologicalData r k).indicator
          (equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
            W.val (Binv i) φ 0) q *
          ∫ h, adjacentRankInnerSliceWeight F Φ χ (m - k) s h * (f i).val h ∂η := by
    funext q
    by_cases hk : q ∈ determinantSlice F.canonicalTopologicalData r k
    · rw [Set.indicator_of_mem hk]
      induction q using Quotient.inductionOn with
      | h g =>
        have hg : F.canonicalTopologicalData.ord
            (GeneralLinear.determinant g : F.Carrier) = k := hk
        have heq (h : Langlands.GeneralLinear (r + 1) F.Carrier) :
            after (Quotient.mk _ g, h) =
              W.val.val g * φ (lastRow g) *
                (adjacentRankInnerSliceWeight F Φ χ (m - k) s h *
                  glModelFunction (ψ.scale (-1)) r τ ℓ' W' (g * h)) :=
          adjacentRankJointShellKernel_mk_eq_innerSlice F ψ W.val Winv Φ φ χ m k s g h hg
        change (∫ h, after (Quotient.mk _ g, h) ∂η) = _
        rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul,
          (hf (m - k) s g).2.2, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Set.indicator_of_mem hk, equalRankIntegrand_zero_mk]
        change _ = W.val.val g * glModelFunction (ψ.scale (-1)) r τ ℓ' (B i) g *
          φ (lastRow g) * _
        ring
    · simp only [Set.indicator_of_notMem hk, zero_mul, Finset.sum_const_zero]
  have hconv :
      (∫ z, after z ∂ν.prod η) = ∑ k ∈ I, ∑ i,
        equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W.val (Binv i) φ k *
          ∫ h, adjacentRankInnerSliceWeight F Φ χ (m - k) s h * (f i).val h ∂η := by
    rw [integral_prod _ ha, integral_eq_sum_determinantSlices F ν outer ho I houterSupport]
    apply Finset.sum_congr rfl
    intro k _
    rw [hpoint k, integral_finsetSum Finset.univ (fun i _ => (hslice k i).mul_const _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_mul_const]
    congr 1
    exact (sliceCoefficient_eq_integral_indicator F.canonicalTopologicalData ν
      (equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        W.val (Binv i) φ 0) k).symm
  refine ⟨hb, ha, hslice, hfi, hconv, ?_⟩
  exact hba.trans ((integral_prod _ ha).symm.trans hconv)

end Langlands.RankinSelberg.Padic
