import Langlands.Representation.RankinSelberg.CorankSliceFiniteEvaluation
import Langlands.AllField.Representation.RankinSelberg.CorankOneEntireSliceStatement
import Langlands.AllField.Representation.RankinSelberg.IntegralDeterminant
/-!
# Finite evaluation of corank-one determinant slices with common compact support

JPSS (1983), Section 4.5, printed pages 408–409. Suppose a family of standard
Whittaker functions on `GL_(r+2)` is right invariant under one open subgroup and
depends analytically on a parameter at each point, and suppose the restrictions to
one determinant slice of all corank-one integrands against a fixed coefficient
on `GL_(r+1)` vanish outside one compact set. Then one compact open subgroup `J`
of `GL_(r+1)` leaves every integrand and the slice invariant, finitely many
pairwise disjoint `J`-orbits carry all the restricted integrands, and each slice
integral is a finite sum of orbit masses times point values, with orbits and
masses independent of the parameter. Hence every slice is integrable and its
coefficient is analytic. The common compact support is a hypothesis here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.CommonLevel
open Langlands.RankinSelberg.CommonLevel hiding corank_slice_of_common_support ord_det_of_mem_integralSubgroup
open Langlands.AllField.RankinSelberg.CommonLevel
open Langlands.RankinSelberg hiding CorankOneEntireSliceStatement EqualRankAnalyticStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_integralSubgroup normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV

/-! ## Right orbits of a subgroup on the left-unipotent quotient -/

section Orbits



end Orbits

section Padic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- An integral invertible matrix has determinant of order zero. -/
theorem ord_det_of_mem_integralSubgroup {r : ℕ}
    {k : Langlands.GeneralLinear (r + 1) F}
    (hk : k ∈ Conductor.integralSubgroup T.Integers r) :
    T.ord (GeneralLinear.determinant k : F) = 0 := by
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have h : (T.residueCardinality : ℝ) ^ (-T.ord (GeneralLinear.determinant k : F)) =
      (T.residueCardinality : ℝ) ^ (-(0 : ℤ)) := by
    rw [← T.normalizedAbs_of_ne_zero (GeneralLinear.determinant k).ne_zero, neg_zero,
      zpow_zero]
    exact normalizedAbs_det_of_mem_integralSubgroup T hk
  exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne' h)

/-- JPSS (1983), Section 4.5, printed pages 408–409, in the corank-one setting,
conditional on common compact support. Let `U` be a family of standard Whittaker
functions on `GL_(r+2)` right invariant under one open subgroup `K` and analytic in
the parameter at each point, and `Wprime` a fixed coefficient of a representation of
Whittaker type on `GL_(r+1)`. If on the slice `S_m` every corank-one integrand at
`s = 0` vanishes outside one compact set `C`, then each of these integrands is
integrable on `S_m` and the slice coefficient is analytic in the parameter. -/
theorem corank_slice_of_common_support (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient r F)
    letI : BorelSpace (LeftUnipotentQuotient r F) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : Measure (LeftUnipotentQuotient r F))
      [IsFiniteMeasureOnCompacts ν]
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V),
      IsOfWhittakerType r (inverseStandardCharacter ψ r) τ →
      ∀ (ℓ : glInverseFunctionals ψ r τ) (Wprime : (coefficientModel τ ℓ).toSubmodule)
        (U : ℂ → WhittakerFunctions ψ (r + 1))
        (K : Subgroup (Langlands.GeneralLinear (r + 1 + 1) F)),
        IsOpen (K : Set (Langlands.GeneralLinear (r + 1 + 1) F)) →
        (∀ (u : ℂ) (g : Langlands.GeneralLinear (r + 1 + 1) F) (k : K),
          (U u).val (g * k) = (U u).val g) →
        (∀ (g : Langlands.GeneralLinear (r + 1 + 1) F) (u : ℂ),
          AnalyticAt ℂ (fun z => (U z).val g) u) →
        ∀ (m : ℤ) (C : Set (LeftUnipotentQuotient r F)), IsCompact C →
          (∀ z : ℂ, Function.support ((determinantSlice T r m).indicator
            (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U z) Wprime.val 0)) ⊆ C) →
          (∀ u : ℂ,
            SliceIntegrableAt T ν
              (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U u) Wprime.val 0) m) ∧
          ∀ u : ℂ,
            AnalyticAt ℂ
              (fun z => sliceCoefficient T ν
                (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U z) Wprime.val 0) m) u := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient r F)
  have : BorelSpace (LeftUnipotentQuotient r F) := ⟨rfl⟩
  intro ψ ν _ V _ _ τ hτ ℓ Wprime U K hKo hKinv hU m C hC hsupp
  let G := Langlands.GeneralLinear (r + 1) F
  let N := upperUnipotent (r + 1) F
  let S := determinantSlice T r m
  let f : ℂ → LeftUnipotentQuotient r F → ℂ := fun z =>
    corankOneIntegrand ψ (normalizedAbsoluteValue T) (U z) Wprime.val 0
  have hCS : IsCompact (C ∩ S) := hC.inter_right (isClosed_determinantSlice T r m)
  have hsuppC : ∀ z, ∀ q ∈ S, f z q ≠ 0 → q ∈ C ∩ S := by
    intro z q hqS hne
    refine ⟨hsupp z ?_, hqS⟩
    rw [Function.mem_support, Set.indicator_of_mem hqS]
    exact hne
  -- One common right level.
  obtain ⟨v, rfl⟩ := modelMap_surjective τ ℓ Wprime
  obtain ⟨K1, hK1⟩ := hτ.1.1 v
  let J : Subgroup G := K1.toSubgroup ⊓ K.comap (rankInclusion 1) ⊓
    Conductor.integralSubgroup (ValuativeRel.valuation F).integer r
  have hKcont : Continuous (rankInclusion (R := F) (n := r + 1) 1) :=
    (GeneralLinear.rankInclusionContinuous (R := F) (n := r + 1) 1).continuous_toFun
  have hIo : IsOpen (Conductor.integralSubgroup (ValuativeRel.valuation F).integer r :
      Set G) := by
    rw [← Conductor.levelSubgroup_zero]
    exact (Conductor.levelOpenSubgroup F r 0).isOpen
  have hIc : IsCompact (Conductor.integralSubgroup (ValuativeRel.valuation F).integer r :
      Set G) := by
    rw [← Conductor.levelSubgroup_zero]
    exact Conductor.isCompact_levelOpenSubgroup F r 0
  have hJo : IsOpen (J : Set G) :=
    (K1.isOpen.inter (hKo.preimage hKcont)).inter hIo
  have hJc : IsCompact (J : Set G) :=
    hIc.of_isClosed_subset (J.isClosed_of_isOpen hJo) fun k hk => hk.2
  -- Invariance of the integrands and of the slice under the common level.
  have hfJ : ∀ z q, ∀ k ∈ J, f z (rightTranslate N k q) = f z q := by
    intro z q k hk
    induction q using Quotient.inductionOn with
    | h g =>
      change (U z).val (rankInclusion 1 (g * k)) * (modelMap τ ℓ v).val.val (g * k) *
          determinantWeight (normalizedAbsoluteValue T) (g * k) (0 - 1 / 2) =
        (U z).val (rankInclusion 1 g) * (modelMap τ ℓ v).val.val g *
          determinantWeight (normalizedAbsoluteValue T) g (0 - 1 / 2)
      have h1 : (U z).val (rankInclusion 1 (g * k)) = (U z).val (rankInclusion 1 g) := by
        rw [map_mul]
        exact hKinv z (rankInclusion 1 g) ⟨rankInclusion 1 k, hk.1.2⟩
      have h2 : (modelMap τ ℓ v).val.val (g * k) = (modelMap τ ℓ v).val.val g := by
        change ℓ.val (τ (g * k) v) = ℓ.val (τ g v)
        rw [map_mul, Module.End.mul_apply]
        congr 2
        exact (Representation.mem_invariants _ v).1 hK1 ⟨k, hk.1.1⟩
      have h3 : determinantWeight (normalizedAbsoluteValue T) (g * k) (0 - 1 / 2) =
          determinantWeight (normalizedAbsoluteValue T) g (0 - 1 / 2) := by
        unfold determinantWeight
        rw [Units.val_mul, Matrix.det_mul, map_mul, normalizedAbsoluteValue_apply T
          (Matrix.det k.val), normalizedAbs_det_of_mem_integralSubgroup T hk.2, mul_one]
      rw [h1, h2, h3]
  have hSJ : ∀ q ∈ S, ∀ k ∈ J, rightTranslate N k q ∈ S := by
    intro q hq k hk
    rw [rightTranslate_mem_determinantSlice, ord_det_of_mem_integralSubgroup T hk.2, sub_zero]
    exact hq
  -- Finitely many disjoint orbits, chosen once for all parameters.
  obtain ⟨u, huC, hdisj, hcover⟩ := exists_finset_rightTranslateOrbit_cover N hJo hCS
  have hmain : ∀ z, IntegrableOn (f z) S ν ∧
      ∫ q in S, f z q ∂ν = ∑ q ∈ u, (ν.real (rightTranslateOrbit N J q) : ℂ) * f z q :=
    fun z => integrableOn_and_setIntegral_eq_sum_rightTranslateOrbit N ν hJo hJc
      (measurableSet_determinantSlice T r m) hSJ u (fun q hq => (huC q hq).2) hdisj (f z)
      (hfJ z) fun q hq hne => hcover (hsuppC z q hq hne)
  refine ⟨fun z => (hmain z).1, fun z0 => ?_⟩
  have heq : (fun z => sliceCoefficient T ν
      (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U z) (modelMap τ ℓ v).val 0) m) =
      fun z => ∑ q ∈ u, (ν.real (rightTranslateOrbit N J q) : ℂ) * f z q :=
    funext fun z => (hmain z).2
  rw [heq]
  refine Finset.analyticAt_fun_sum _ fun q _ => analyticAt_const.mul ?_
  induction q using Quotient.inductionOn with
  | h g =>
    exact ((hU (rankInclusion 1 g) z0).mul analyticAt_const).mul analyticAt_const

end Padic

end Langlands.AllField.RankinSelberg.CommonLevel
