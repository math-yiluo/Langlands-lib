import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictContinuation
import Langlands.Representation.RankinSelberg.TwoBlockDominantDiagonalSupport
import Langlands.Representation.RankinSelberg.UnequalRankBlockSpanProof
import Langlands.Representation.RankinSelberg.UnequalRankCompactSupportProof
import Langlands.Representation.RankinSelberg.CorankSliceFiniteEvaluation
import Langlands.Representation.RankinSelberg.AdjacentRankParameterSpecialization

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open HarmonicAnalysis.BilateralLaurentSeries ParameterSpecialization

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance strictEntireTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictEntireValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictEntireLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictEntireT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance strictEntireSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance strictEntireSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance strictEntireMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictEntireBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictEntireGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance strictEntireGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictEntireUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance strictEntireUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictEntireQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictEntireQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩


open CommonLevel TwoBlockDominantFirstBlock AdjacentBlockReduction

local notation "T" => F.canonicalTopologicalData
local notation "abv" => normalizedAbsoluteValue T

/-- The literal fixed-rank coefficient is the actual integral at zero with its
quotient measure restricted to the determinant slice. -/
theorem strictSliceCoefficient_eq_restrictedIntegral {n r j k : ℕ}
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier)
    (U : WhittakerFunctions ψ r) (U' : InverseWhittakerFunctions ψ n) (a : ℤ) :
    strictSliceCoefficient F hr ψ μ ν U U' a =
      unequalRankIntegralAt j k hr ψ abv (μ.restrict (determinantSlice T n a))
        (rectangularMeasure ν j (n + 1)) U U' 0 := by
  subst r
  exact congrFun (strictIntegral_eq F rfl ψ
    (μ.restrict (determinantSlice T n a)) ν U U') 0

private theorem strictEntire_continuous_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F.Carrier) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (rankInclusionContinuous 1).continuous.comp ih

section ZeroRows

variable {n k : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
  (μ : Measure (LeftUnipotentQuotient n F.Carrier))
  (ν : AdditiveHaarMeasure F.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
  (hπ : IsSmooth π) (lambda : glFunctionals ψ (n + (0 + k + 1)) π)
  (W : (coefficientModel π lambda).toSubmodule)
  (U : ℂ → InverseWhittakerFunctions ψ n)
  (K : Subgroup (GeneralLinear (n + 1) F.Carrier))
  (hKo : IsOpen (K : Set (GeneralLinear (n + 1) F.Carrier)))
  (hK : ∀ (u : ℂ) (g : GeneralLinear (n + 1) F.Carrier) (k : K),
    (U u).val (g * k) = (U u).val g)
  (hU : ∀ (g : GeneralLinear (n + 1) F.Carrier) (u : ℂ),
    AnalyticAt ℂ (fun z => (U z).val g) u)

include hπ K hKo hK hU

set_option maxHeartbeats 1600000 in
/-- At zero rectangular rows, compact diagonal slice support and a common right
level express every actual coefficient as a finite sum of entire point values. -/
theorem strictZeroRowSlice_entire [IsFiniteMeasureOnCompacts μ] :
    EntireCoefficientFamily (fun u => strictSliceCoefficient F rfl ψ μ ν W.val (U u)) := by
  classical
  obtain ⟨K1, hK1⟩ := model_isSmooth π hπ lambda W
  let G := GeneralLinear (n + 1) F.Carrier
  let N := upperUnipotent (n + 1) F.Carrier
  let J : Subgroup G := K1.toSubgroup.comap (appendIdentity n (0 + k + 1)) ⊓ K ⊓
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
    ((K1.isOpen.preimage (strictEntire_continuous_appendIdentity F n (0 + k + 1))).inter hKo).inter hIo
  have hJc : IsCompact (J : Set G) :=
    hIc.of_isClosed_subset (J.isClosed_of_isOpen hJo) fun z hz => hz.2
  let ρ := strictRectangleMeasure F ν 0 (n + 1)
  let f : ℂ → LeftUnipotentQuotient n F.Carrier → ℂ := fun z =>
    unequalRankAverage F 0 k ψ ρ W.val (U z) 0
  have hf (z : ℂ) (g : G) : f z (Quotient.mk _ g) =
      (ρ.real Set.univ : ℂ) * W.val.val (appendIdentity n (0 + k + 1) g) *
        (U z).val g * determinantWeight abv g (0 - ((0 + k + 1 : ℕ) : ℂ) / 2) := by
    simp only [f, unequalRankAverage, unequalRankIntegrand_mk,
      unequalRankMatrix_zero_rows, integral_const, Complex.real_smul]
    ring
  have hfJ : ∀ z q, ∀ a ∈ J, f z (rightTranslate N a q) = f z q := by
    intro z q a ha
    induction q using Quotient.inductionOn with
    | h g =>
      change f z (Quotient.mk _ (g * a)) = f z (Quotient.mk _ g)
      rw [hf, hf, map_mul]
      have hW : W.val.val (appendIdentity n (0 + k + 1) g * appendIdentity n (0 + k + 1) a) =
          W.val.val (appendIdentity n (0 + k + 1) g) :=
        congrArg (fun f : (coefficientModel π lambda).toSubmodule =>
          f.val.val (appendIdentity n (0 + k + 1) g)) (hK1 ⟨_, ha.1.1⟩)
      rw [hW, hK z g ⟨a, ha.1.2⟩]
      have hd : determinantWeight abv (g * a) (0 - ((0 + k + 1 : ℕ) : ℂ) / 2) =
          determinantWeight abv g (0 - ((0 + k + 1 : ℕ) : ℂ) / 2) := by
        unfold determinantWeight
        rw [Units.val_mul, Matrix.det_mul, map_mul, normalizedAbsoluteValue_apply T
          (Matrix.det a.val), normalizedAbs_det_of_mem_integralSubgroup T ha.2, mul_one]
      rw [hd]
  intro a z0
  let S := determinantSlice T n a
  let normProfile : LeftUnipotentQuotient n F.Carrier → ℝ :=
    S.indicator (whittakerNorm ψ (diagonalWhittaker ψ (0 + k + 1) W.val))
  let C := tsupport normProfile
  have hC : IsCompact C :=
    (diagonalWhittaker_slice_hasCompactSupport F n (0 + k) ψ π hπ lambda W a).isCompact
  have hCS : IsCompact (C ∩ S) := hC.inter_right (isClosed_determinantSlice T n a)
  have hsuppC : ∀ z, ∀ q ∈ S, f z q ≠ 0 → q ∈ C ∩ S := by
    intro z q hq hne
    refine ⟨subset_tsupport normProfile ?_, hq⟩
    change normProfile q ≠ 0
    dsimp only [normProfile]
    rw [Set.indicator_of_mem hq]
    induction q using Quotient.inductionOn with
    | h g =>
      rw [whittakerNorm_mk]
      apply norm_ne_zero_iff.mpr
      intro hz
      apply hne
      rw [hf]
      change (ρ.real Set.univ : ℂ) * (diagonalWhittaker ψ (0 + k + 1) W.val).val g *
        (U z).val g * _ = 0
      rw [hz, mul_zero, zero_mul, zero_mul]
  have hSJ : ∀ q ∈ S, ∀ a ∈ J, rightTranslate N a q ∈ S := by
    intro q hq a ha
    rw [rightTranslate_mem_determinantSlice, ord_det_of_mem_integralSubgroup T ha.2, sub_zero]
    exact hq
  obtain ⟨points, hpC, hdisj, hcover⟩ := exists_finset_rightTranslateOrbit_cover N hJo hCS
  have horbit : ∀ z, IntegrableOn (f z) S μ ∧
      ∫ q in S, f z q ∂μ =
        ∑ q ∈ points, (μ.real (rightTranslateOrbit N J q) : ℂ) * f z q :=
    fun z => integrableOn_and_setIntegral_eq_sum_rightTranslateOrbit N μ hJo hJc
      (measurableSet_determinantSlice T n a) hSJ points (fun q hq => (hpC q hq).2)
      hdisj (f z) (hfJ z) fun q hq hne => hcover (hsuppC z q hq hne)
  have heq : (fun z => strictSliceCoefficient F rfl ψ μ ν W.val (U z) a) =
      fun z => ∑ q ∈ points, (μ.real (rightTranslateOrbit N J q) : ℂ) * f z q :=
    funext fun z => (horbit z).2
  rw [heq]
  refine Finset.analyticAt_fun_sum _ fun q _ => analyticAt_const.mul ?_
  induction q using Quotient.inductionOn with
  | h g =>
    change AnalyticAt ℂ (fun z => f z (Quotient.mk _ g)) z0
    simp_rw [hf]
    exact ((analyticAt_const.mul (hU g z0)).mul analyticAt_const)

end ZeroRows

/-- The literal fixed-rank determinant-slice coefficient family is entire. -/
def StrictRankEntireSliceData {n r j k : ℕ}
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier)
    (W : WhittakerFunctions ψ r) (U : ℂ → InverseWhittakerFunctions ψ n) : Prop :=
  EntireCoefficientFamily (fun u => strictSliceCoefficient F hr ψ μ ν W (U u))

set_option maxHeartbeats 1600000 in
/-- Entire point values at one common right level give entire actual strict
slice coefficients at every rectangular row. Full type supplies the uniform
rectangular support used to integrate each row within the original model. -/
theorem strictSlices_entire {n r j k : ℕ}
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier)) [IsFiniteMeasureOnCompacts μ]
    (ν : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π) (hlambda : lambda.val ≠ 0)
    (W : (coefficientModel π lambda).toSubmodule)
    (U : ℂ → InverseWhittakerFunctions ψ n)
    (K : Subgroup (GeneralLinear (n + 1) F.Carrier))
    (hKo : IsOpen (K : Set (GeneralLinear (n + 1) F.Carrier)))
    (hK : ∀ (u : ℂ) (g : GeneralLinear (n + 1) F.Carrier) (a : K),
      (U u).val (g * a) = (U u).val g)
    (hU : ∀ (g : GeneralLinear (n + 1) F.Carrier) (u : ℂ),
      AnalyticAt ℂ (fun z => (U z).val g) u) :
    StrictRankEntireSliceData F hr ψ μ ν W.val U := by
  classical
  induction j generalizing k W with
  | zero =>
    subst r
    exact strictZeroRowSlice_entire F ψ μ ν π hπ.1.1 lambda W U K hKo hK hU
  | succ j ih =>
    have hs : ∃ C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F.Carrier),
        IsCompact C ∧ ∀ g X, W.val.val (blockMatrixAt (j + 1) k hr g X) ≠ 0 → X ∈ C := by
      subst r
      exact unequalRankCompactSupport F T n (j + 1) k ψ V π hπ lambda hlambda W
    obtain ⟨C, hC, hs⟩ := hs
    have hr' : r = n + (j + (k + 1) + 1) := by omega
    obtain ⟨W0, hW0⟩ := exists_adjacent_block_integral_coefficient ν n r j k hr hr'
      ψ π hπ.1.1 lambda W C hC hs
    have hcoef (z : ℂ) (a : ℤ) :
        strictSliceCoefficient F hr ψ μ ν W.val (U z) a =
          strictSliceCoefficient F hr' ψ μ ν W0.val (U z) a := by
      rw [strictSliceCoefficient_eq_restrictedIntegral,
        strictSliceCoefficient_eq_restrictedIntegral,
        unequalRankIntegralAt_eq_outer, unequalRankIntegralAt_eq_outer]
      have hd : j + 1 + k + 1 = j + (k + 1) + 1 := by omega
      apply integral_congr_ae
      filter_upwards [] with q
      rw [hW0 q.out, hd]
    have hi := ih hr' W0
    intro a z
    have heq : (fun u => strictSliceCoefficient F hr ψ μ ν W.val (U u) a) =
        fun u => strictSliceCoefficient F hr' ψ μ ν W0.val (U u) a :=
      funext fun u => hcoef u a
    rw [heq]
    exact hi a z

end Langlands.RankinSelberg.DominantRankTransport
