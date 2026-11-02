import Langlands.Representation.RankinSelberg.CorankSliceFiniteEvaluation
import Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof
import Langlands.HarmonicAnalysis.RowTestSmoothProof

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration CommonLevel

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalEntireTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalEntireValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalEntireLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalEntireT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalEntireQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalEntireQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "abv" => normalizedAbsoluteValue T

variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
  (μ : Measure (LeftUnipotentQuotient n F.Carrier))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
  (lambda : glFunctionals ψ n π)
  (W : (coefficientModel π lambda).toSubmodule)
  (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
  (U : ℂ → InverseWhittakerFunctions ψ n)

/-- Actual equal-rank determinant slices are integrable and their literal
coefficients are entire in the family parameter. -/
def EqualRankEntireSliceData : Prop :=
  (∀ u : ℂ, SliceIntegrable T μ (equalRankIntegrand ψ abv W.val (U u) Φ 0)) ∧
    ∀ (m : ℤ) (u : ℂ),
      AnalyticAt ℂ (fun z => equalRankSliceCoefficient T μ ψ W.val (U z) Φ m) u

set_option maxHeartbeats 1600000 in
/-- Fixed smooth row data supply common compact support. One common right
level then gives a finite orbit formula, so each coefficient is entire. -/
theorem equalRankEntireSliceData [IsFiniteMeasureOnCompacts μ]
    (hπ : IsSmooth π)
    (K : Subgroup (GeneralLinear (n + 1) F.Carrier))
    (hKo : IsOpen (K : Set (GeneralLinear (n + 1) F.Carrier)))
    (hK : ∀ (u : ℂ) (g : GeneralLinear (n + 1) F.Carrier) (k : K),
      (U u).val (g * k) = (U u).val g)
    (hU : ∀ (g : GeneralLinear (n + 1) F.Carrier) (u : ℂ),
      AnalyticAt ℂ (fun z => (U z).val g) u) :
    EqualRankEntireSliceData F ψ μ π lambda W Φ U := by
  classical
  obtain ⟨v, hv⟩ := modelMap_surjective π lambda W
  obtain ⟨K1, hK1⟩ := hπ v
  obtain ⟨KΦ, hKΦ⟩ := rowTestSmooth F.Carrier (n + 1) Φ
  let G := GeneralLinear (n + 1) F.Carrier
  let N := upperUnipotent (n + 1) F.Carrier
  let J : Subgroup G := K1.toSubgroup ⊓ K ⊓ KΦ.toSubgroup ⊓
    Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  have hIo : IsOpen
      (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n : Set G) := by
    rw [← Conductor.levelSubgroup_zero]
    exact (Conductor.levelOpenSubgroup F.Carrier n 0).isOpen
  have hIc : IsCompact
      (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n : Set G) := by
    rw [← Conductor.levelSubgroup_zero]
    exact Conductor.isCompact_levelOpenSubgroup F.Carrier n 0
  have hJo : IsOpen (J : Set G) :=
    ((K1.isOpen.inter hKo).inter KΦ.isOpen).inter hIo
  have hJc : IsCompact (J : Set G) :=
    hIc.of_isClosed_subset (J.isClosed_of_isOpen hJo) fun k hk => hk.2
  let f : ℂ → LeftUnipotentQuotient n F.Carrier → ℂ := fun z =>
    equalRankIntegrand ψ abv W.val (U z) Φ 0
  have hfJ : ∀ z q, ∀ k ∈ J, f z (rightTranslate N k q) = f z q := by
    intro z q k hk
    induction q using Quotient.inductionOn with
    | h g =>
      change equalRankIntegrand ψ abv W.val (U z) Φ 0 (Quotient.mk _ (g * k)) =
        equalRankIntegrand ψ abv W.val (U z) Φ 0 (Quotient.mk _ g)
      rw [equalRankIntegrand_zero_mk, equalRankIntegrand_zero_mk]
      have hW : W.val.val (g * k) = W.val.val g := by
        rw [← hv]
        change lambda.val (π (g * k) v) = lambda.val (π g v)
        rw [map_mul, Module.End.mul_apply]
        congr 2
        exact (Representation.mem_invariants _ v).1 hK1 ⟨k, hk.1.1.1⟩
      rw [hW, hK z g ⟨k, hk.1.1.2⟩, lastRow_mul_eq_vecMul,
        hKΦ k hk.1.2]
  have hmain : ∀ m : ℤ,
      (∀ z, SliceIntegrableAt T μ (f z) m) ∧
      ∀ z0, AnalyticAt ℂ (fun z => sliceCoefficient T μ (f z) m) z0 := by
    intro m
    let S := determinantSlice T n m
    let rowNorm : LeftUnipotentQuotient n F.Carrier → ℝ :=
      S.indicator (fun q => whittakerNorm ψ W.val q * ‖Φ (quotientLastRow n q)‖)
    have hc := whittakerRowSliceCompactSupport F T n ψ V π hπ lambda W Φ m
    let C := tsupport rowNorm
    have hC : IsCompact C := hc.isCompact
    have hCS : IsCompact (C ∩ S) := hC.inter_right (isClosed_determinantSlice T n m)
    have hsuppC : ∀ z, ∀ q ∈ S, f z q ≠ 0 → q ∈ C ∩ S := by
      intro z q hq hne
      refine ⟨subset_tsupport rowNorm ?_, hq⟩
      change rowNorm q ≠ 0
      dsimp only [rowNorm]
      rw [Set.indicator_of_mem hq]
      induction q using Quotient.inductionOn with
      | h g =>
        rw [whittakerNorm_mk, quotientLastRow_mk]
        change equalRankIntegrand ψ abv W.val (U z) Φ 0 (Quotient.mk _ g) ≠ 0 at hne
        rw [equalRankIntegrand_zero_mk] at hne
        have hW : W.val.val g ≠ 0 := fun h => hne (by rw [h, zero_mul, zero_mul])
        have hΦ : Φ (lastRow g) ≠ 0 := fun h => hne (by rw [h, mul_zero])
        exact mul_ne_zero (norm_ne_zero_iff.mpr hW) (norm_ne_zero_iff.mpr hΦ)
    have hSJ : ∀ q ∈ S, ∀ k ∈ J, rightTranslate N k q ∈ S := by
      intro q hq k hk
      rw [rightTranslate_mem_determinantSlice, ord_det_of_mem_integralSubgroup T hk.2,
        sub_zero]
      exact hq
    obtain ⟨points, hpC, hdisj, hcover⟩ := exists_finset_rightTranslateOrbit_cover N hJo hCS
    have horbit : ∀ z, IntegrableOn (f z) S μ ∧
        ∫ q in S, f z q ∂μ =
          ∑ q ∈ points, (μ.real (rightTranslateOrbit N J q) : ℂ) * f z q :=
      fun z => integrableOn_and_setIntegral_eq_sum_rightTranslateOrbit N μ hJo hJc
        (measurableSet_determinantSlice T n m) hSJ points (fun q hq => (hpC q hq).2)
        hdisj (f z) (hfJ z) fun q hq hne => hcover (hsuppC z q hq hne)
    refine ⟨fun z => (horbit z).1, fun z0 => ?_⟩
    have heq : (fun z => sliceCoefficient T μ (f z) m) =
        fun z => ∑ q ∈ points, (μ.real (rightTranslateOrbit N J q) : ℂ) * f z q :=
      funext fun z => (horbit z).2
    rw [heq]
    refine Finset.analyticAt_fun_sum _ fun q _ => analyticAt_const.mul ?_
    induction q using Quotient.inductionOn with
    | h g =>
      change AnalyticAt ℂ
        (fun z => equalRankIntegrand ψ abv W.val (U z) Φ 0 (Quotient.mk _ g)) z0
      simp only [equalRankIntegrand_zero_mk]
      exact (analyticAt_const.mul (hU g z0)).mul analyticAt_const
  exact ⟨fun z m => (hmain m).1 z, fun m z => (hmain m).2 z⟩

end Langlands.RankinSelberg.DominantRankTransport
