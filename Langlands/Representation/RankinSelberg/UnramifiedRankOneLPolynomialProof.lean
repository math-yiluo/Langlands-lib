import Langlands.Representation.Unramified.PrincipalSeries
import Langlands.Representation.GodementJacquet.ModelMatrixNormalizedGenerator
import Langlands.Representation.GodementJacquet.TateMatrixAnalyticData
import Langlands.Representation.GodementJacquet.CoefficientTransport
import Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof
import Langlands.Representation.RankinSelberg.UniformFiniteFunctionMellinConvergenceProof

/-! # The rank-one L-polynomial of an unramified character -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GodementJacquet Polynomial Whittaker

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance unramifiedRankOneLPolynomialTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance unramifiedRankOneLPolynomialValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance unramifiedRankOneLPolynomialLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance unramifiedRankOneLPolynomialT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance unramifiedRankOneLPolynomialFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance unramifiedRankOneLPolynomialFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance unramifiedRankOneLPolynomialUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance unramifiedRankOneLPolynomialUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩

private theorem normalizedAbs_cpow_eq_spectral_zpow (a : F.Carrierˣ) (s : ℂ) :
    (F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℂ) ^ s =
      spectralPoint F.canonicalTopologicalData.residueCardinality s ^
        F.canonicalTopologicalData.ord (a : F.Carrier) := by
  let q := F.canonicalTopologicalData.residueCardinality
  let k := F.canonicalTopologicalData.ord (a : F.Carrier)
  have hq : 0 < q := lt_trans zero_lt_one
    F.canonicalTopologicalData.residueCardinality_gt_one
  have harg : Complex.arg (F.canonicalTopologicalData.residueCardinality : ℂ) = 0 := by
    simpa only [Complex.ofReal_natCast] using
      Complex.arg_ofReal_of_nonneg (show 0 ≤ (q : ℝ) by positivity)
  rw [F.canonicalTopologicalData.normalizedAbs_of_ne_zero a.ne_zero,
    Complex.ofReal_zpow, Complex.ofReal_natCast,
    ← Complex.cpow_int_mul' (by simp [harg, Real.pi_pos])
      (by simpa only [harg, mul_zero] using Real.pi_pos.le)]
  change (q : ℂ) ^ ((-k : ℤ) * s) = ((q : ℂ) ^ (-s)) ^ k
  rw [← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

private theorem exists_spectral_threshold {q : ℕ} (hq : 1 < q) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ c : ℝ, ∀ s : ℂ, c < s.re → ‖spectralPoint q s‖ < ρ := by
  have hq0 : 0 < q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  refine ⟨-Real.log ρ / Real.log q, fun s hs => ?_⟩
  rw [spectralPoint, Complex.norm_natCast_cpow_of_pos hq0, Complex.neg_re,
    Real.rpow_def_of_pos (by exact_mod_cast hq0), ← Real.lt_log_iff_exp_lt hρ]
  rw [div_lt_iff₀ hlogq] at hs
  linarith

private theorem ord_eq_zero_of_mem_integralUnits (u : F.Carrierˣ)
    (hu : u ∈ integralUnits (ValuativeRel.valuation F.Carrier).integer) :
    F.canonicalTopologicalData.ord (u : F.Carrier) = 0 := by
  obtain ⟨π, hπ, hzero, _⟩ :=
    valuationShellIntegration p inferInstance F F.canonicalTopologicalData
  exact (Set.ext_iff.mp hzero u).mpr hu

private def unramifiedRecurrence (z : ℂ) : LinearRecurrence ℂ where
  order := 1
  coeffs := fun _ => z

/-- The exact linear polynomial clears every unramified scalar Mellin value. -/
theorem unramifiedScalarMellin_clears (z : ℂˣ) :
    ∀ R ∈ scalarMellinRationalValues F.canonicalTopologicalData.residueCardinality
      F.canonicalTopologicalData.normalizedAbs (localMultiplicativeHaar F.Carrier)
      (fun a => (Unramified.character F z a : ℂ)) 1,
      ∃ A : LaurentCoefficients,
        laurentToRatFunc A =
          algebraMap ℂ[X] RationalFunctions (1 - C (z : ℂ) * X) * R := by
  let T := F.canonicalTopologicalData
  let η : F.Carrierˣ → ℂ := fun a => Unramified.character F z a
  let μ := localMultiplicativeHaar F.Carrier
  let K : Set F.Carrierˣ :=
    (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ)
  have hKμ : μ.real K = 1 := by simp [μ, K, Measure.real]
  have hKm : MeasurableSet K :=
    (integralUnits_isOpen _ Valuation.isOpen_integer).measurableSet
  obtain ⟨π, _E, B, hπ, hB, htests⟩ := finiteFunctionShellSeries p inferInstance F T η
    (Units.continuous_val.comp (Unramified.character F z).continuous)
    (GodementJacquet.tateCharacter_translationFinite (Unramified.character F z))
  let E := unramifiedRecurrence (z : ℂ)
  obtain ⟨_, ρ, hρ, hweights⟩ :=
    Analysis.eventuallyRecurrentLaurentSeriesStatement_proof E
  obtain ⟨_, hrepresent⟩ := hweights 1 zero_lt_one
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨c0, hc0⟩ := exists_spectral_threshold T.residueCardinality_gt_one
    (lt_min (one_div_pos.mpr hBpos) hρ)
  intro R hR
  obtain ⟨Φ, hΦR⟩ := hR
  let c : ℤ → ℂ := fun n =>
    ∫ u in K, Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier) * η (π ^ n * u) ∂μ
  obtain ⟨L, N, hLN, hlow, _, hintegral⟩ := htests Φ
  obtain ⟨LΦ, NΦ, CΦ, hLNΦ, hCΦ, hΦbound, hΦlow, hΦhigh⟩ :=
    schwartzBruhatValuationBounds p F T Φ
  have hord (n : ℤ) (u : F.Carrierˣ) (hu : u ∈ K) :
      T.ord ((π ^ n * u : F.Carrierˣ) : F.Carrier) = n := by
    rw [Units.val_mul, T.ord_mul (π ^ n).ne_zero u.ne_zero,
      Units.val_zpow_eq_zpow_val, T.ord_zpow, hπ,
      ord_eq_zero_of_mem_integralUnits F u hu, mul_one, add_zero]
  have hhigh (n : ℤ) (hn : (NΦ : ℤ) ≤ n) :
      c n = Φ 0 * (z : ℂ) ^ n := by
    change (∫ u in K, _ ∂μ) = _
    calc
      _ = ∫ _u in K, Φ 0 * (z : ℂ) ^ n ∂μ :=
        setIntegral_congr_fun hKm fun u hu => by
          rw [hΦhigh _ (by rw [hord n u hu]; exact hn)]
          simp only [η, Unramified.character_apply, Units.val_zpow_eq_zpow_val]
          change Φ 0 * (z : ℂ) ^ T.ord ((π ^ n * u : F.Carrierˣ) : F.Carrier) = _
          rw [hord n u hu]
      _ = _ := by rw [setIntegral_const, hKμ]; simp
  have hrec : E.IsSolution (fun j : ℕ => c ((j : ℤ) + (max N NΦ : ℕ))) := by
    intro j
    change c (((j + 1 : ℕ) : ℤ) + (max N NΦ : ℕ)) =
      ∑ i : Fin 1, (z : ℂ) * c (((j + i : ℕ) : ℤ) + (max N NΦ : ℕ))
    simp only [Fin.sum_univ_one, Fin.val_zero, Nat.add_zero]
    rw [hhigh _ (by omega), hhigh _ (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (j : ℤ) + 1 + (max N NΦ : ℕ) =
      ((j : ℤ) + (max N NΦ : ℕ)) + 1 by omega,
      zpow_add₀ z.ne_zero]
    simp only [zpow_one]
    ring
  obtain ⟨S, A, hclear, heval⟩ :=
    hrepresent c L (max N NΦ) (by omega) hlow hrec
  have hcont : HasRationalContinuation T.residueCardinality
      (scalarMellinIntegral T.normalizedAbs μ η 1 Φ) S := by
    refine ⟨c0, fun s hs => ?_⟩
    have hz := spectralPoint_ne_zero T.residueCardinality_gt_one s
    have hsmall := hc0 s hs
    have hBz : B * ‖spectralPoint T.residueCardinality s‖ < 1 := by
      have := (lt_div_iff₀ hBpos).mp (hsmall.trans_le (min_le_left _ _))
      nlinarith
    obtain ⟨_, _, hI⟩ := hintegral _ hz hBz
    obtain ⟨_, hS, hsum⟩ := heval _ hz (by
      simpa only [pow_one] using (hsmall.trans_le (min_le_right _ _)))
    refine ⟨hS, ?_⟩
    simp only [scalarMellinIntegral, scalarMellinIntegrand, Nat.cast_one, one_mul]
    simp only [T, normalizedAbs_cpow_eq_spectral_zpow F]
    exact hI.trans (by simpa only [pow_one] using hsum)
  refine ⟨A, ?_⟩
  rw [hΦR.unique T.residueCardinality_gt_one hcont]
  have hQ : (1 - ∑ i : Fin E.order,
      C (E.coeffs i) * X ^ (E.order - (i : ℕ))) = 1 - C (z : ℂ) * X := by
    change (1 - ∑ i : Fin 1, C (z : ℂ) * X ^ (1 - (i : ℕ))) = _
    simp only [Fin.sum_univ_one, Fin.val_zero, Nat.sub_zero, pow_one]
  rw [hQ, pow_one, Polynomial.comp_X, laurentToRatFunc_toLaurent] at hclear
  exact hclear

/-- The integer-ring test attains the reciprocal of the unramified polynomial. -/
theorem unramifiedScalarMellin_reciprocal_mem (z : ℂˣ) :
    (algebraMap ℂ[X] RationalFunctions (1 - C (z : ℂ) * X))⁻¹ ∈
      scalarMellinRationalValues F.canonicalTopologicalData.residueCardinality
        F.canonicalTopologicalData.normalizedAbs (localMultiplicativeHaar F.Carrier)
        (fun a => (Unramified.character F z a : ℂ)) 1 := by
  classical
  let T := F.canonicalTopologicalData
  let η : F.Carrierˣ → ℂ := fun a => Unramified.character F z a
  let μ := localMultiplicativeHaar F.Carrier
  let K : Set F.Carrierˣ :=
    (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ)
  let O : Set F.Carrier := T.Integers
  have hOc : IsCompact O := T.isCompact_integers
  have hOo : IsClopen O := ⟨hOc.isClosed, T.isOpen_integers⟩
  let Φ := UniformMellin.clopenIndicator O hOc hOo
  have hKμ : μ.real K = 1 := by simp [μ, K, Measure.real]
  have hKm : MeasurableSet K :=
    (integralUnits_isOpen _ Valuation.isOpen_integer).measurableSet
  obtain ⟨π, _E, B, hπ, hB, htests⟩ := finiteFunctionShellSeries p inferInstance F T η
    (Units.continuous_val.comp (Unramified.character F z).continuous)
    (GodementJacquet.tateCharacter_translationFinite (Unramified.character F z))
  have hord (n : ℤ) (u : F.Carrierˣ) (hu : u ∈ K) :
      T.ord ((π ^ n * u : F.Carrierˣ) : F.Carrier) = n := by
    rw [Units.val_mul, T.ord_mul (π ^ n).ne_zero u.ne_zero,
      Units.val_zpow_eq_zpow_val, T.ord_zpow, hπ,
      ord_eq_zero_of_mem_integralUnits F u hu, mul_one, add_zero]
  have hΦ (n : ℤ) (u : F.Carrierˣ) (hu : u ∈ K) :
      Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier) = if 0 ≤ n then 1 else 0 := by
    have hmem : ((π ^ n * u : F.Carrierˣ) : F.Carrier) ∈ O ↔ 0 ≤ n := by
      change _ ∈ T.Integers ↔ _
      rw [← T.normalizedAbs_le_one_iff_mem_integers,
        T.normalizedAbs_of_ne_zero (π ^ n * u).ne_zero, hord n u hu,
        zpow_le_one_iff_right₀ (show (1 : ℝ) < T.residueCardinality by
          exact_mod_cast T.residueCardinality_gt_one)]
      omega
    change O.indicator (fun _ => (1 : ℂ)) _ = _
    by_cases hn : 0 ≤ n
    · rw [Set.indicator_of_mem (hmem.mpr hn), ite_eq_left hn]
    · rw [Set.indicator_of_notMem (fun hm => hn (hmem.mp hm)), ite_eq_right hn]
  let c : ℤ → ℂ := fun n =>
    ∫ u in K, Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier) * η (π ^ n * u) ∂μ
  have hc (n : ℤ) : c n = if 0 ≤ n then (z : ℂ) ^ n else 0 := by
    calc
      c n = ∫ _u in K, (if 0 ≤ n then (1 : ℂ) else 0) * (z : ℂ) ^ n ∂μ := by
        apply setIntegral_congr_fun hKm
        intro u hu
        dsimp only
        rw [hΦ n u hu]
        simp only [η, Unramified.character_apply, Units.val_zpow_eq_zpow_val]
        change _ * (z : ℂ) ^ T.ord ((π ^ n * u : F.Carrierˣ) : F.Carrier) = _
        rw [hord n u hu]
      _ = _ := by
        rw [setIntegral_const, hKμ, one_smul]
        split_ifs <;> simp
  obtain ⟨_L, _N, _, _, _, hintegral⟩ := htests Φ
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hzpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  obtain ⟨c0, hc0⟩ := exists_spectral_threshold T.residueCardinality_gt_one
    (lt_min (one_div_pos.mpr hBpos) (one_div_pos.mpr hzpos))
  refine ⟨Φ, c0, fun s hs => ?_⟩
  let w := spectralPoint T.residueCardinality s
  have hw := spectralPoint_ne_zero T.residueCardinality_gt_one s
  have hsmall := hc0 s hs
  have hBw : B * ‖w‖ < 1 := by
    have := (lt_div_iff₀ hBpos).mp (hsmall.trans_le (min_le_left _ _))
    nlinarith
  have hzw : ‖(z : ℂ) * w‖ < 1 := by
    rw [norm_mul]
    have := (lt_div_iff₀ hzpos).mp (hsmall.trans_le (min_le_right _ _))
    nlinarith
  have hD : (1 - C (z : ℂ) * X).eval w ≠ 0 := by
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
    intro h
    have hz1 : (z : ℂ) * w = 1 := (sub_eq_zero.mp h).symm
    rw [hz1, norm_one] at hzw
    exact (lt_irrefl _) hzw
  obtain ⟨hreg, heval⟩ := regular_and_eval_div w 1 (1 - C (z : ℂ) * X) hD
  refine ⟨by simpa only [map_one, one_div] using hreg, ?_⟩
  have htail : Summable (fun j : ℕ => c ((j : ℤ) + (0 : ℤ)) * w ^ ((j : ℤ) + 0)) := by
    simpa only [add_zero, hc, Int.natCast_nonneg, ite_true, zpow_natCast, ← mul_pow] using
      (summable_geometric_of_norm_lt_one hzw)
  obtain ⟨_, hsplit⟩ :=
    Analysis.EventuallyRecurrentLaurentSeries.summable_and_tsum_split
      (fun n : ℤ => c n * w ^ n) 0 0
      (fun n hn => by rw [hc, ite_eq_right (by omega), zero_mul]) htail
  have hsum : ∑' n : ℤ, c n * w ^ n = (1 - (z : ℂ) * w)⁻¹ := by
    simpa only [Int.natCast_zero, Finset.Ico_self, Finset.sum_empty, zero_add,
      add_zero, hc, Int.natCast_nonneg, ite_true, zpow_natCast, ← mul_pow] using
      hsplit.trans (by simpa only [Int.natCast_zero, Finset.Ico_self,
        Finset.sum_empty, zero_add, add_zero, hc, Int.natCast_nonneg, ite_true,
        zpow_natCast, ← mul_pow] using (tsum_geometric_of_norm_lt_one hzw))
  obtain ⟨_, _, hI⟩ := hintegral w hw hBw
  simp only [scalarMellinIntegral, scalarMellinIntegrand, Nat.cast_one, one_mul]
  simp only [normalizedAbs_cpow_eq_spectral_zpow F]
  calc
    _ = ∑' n : ℤ, c n * w ^ n := hI
    _ = (1 - (z : ℂ) * w)⁻¹ := hsum
    _ = _ := by simpa using heval.symm

/-- Exact normalized generator for all actual unramified scalar Mellin tests. -/
theorem unramifiedScalarMellin_isNormalizedGenerator (z : ℂˣ) :
    IsNormalizedGenerator
      (scalarMellinRationalValues F.canonicalTopologicalData.residueCardinality
        F.canonicalTopologicalData.normalizedAbs (localMultiplicativeHaar F.Carrier)
        (fun a => (Unramified.character F z a : ℂ)) 1)
      (1 - C (z : ℂ) * X) := by
  rw [isNormalizedGenerator_iff]
  exact ⟨by simp, unramifiedScalarMellin_clears F z,
    mem_zetaSpan (unramifiedScalarMellin_reciprocal_mem F z)⟩

private theorem scalarRepresentation_isIrreducible {G : Type*} [Group G]
    (σ : Representation ℂ G ℂ) : Representation.IsIrreducible σ := by
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact (bot_ne_top : (⊥ : Submodule ℂ ℂ) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)
  · intro S
    rcases eq_bot_or_eq_top S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- Every supplied symmetric pair certificate for the unramified rank-one
character and the trivial character has the exact linear polynomial.
The additive character and additive Haar measure are arbitrary. -/
theorem unramifiedRankOneLPolynomial_eq
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (z : ℂˣ) {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν
      (characterRepresentation
        (Correspondence.determinantQuasiCharacter F 1 (Unramified.character F z)))
      (characterRepresentation (Correspondence.determinantQuasiCharacter F 1 1)) P) :
    P = 1 - C (z : ℂ) * X := by
  let σ := rankOneCharacter ((Unramified.character F z) : F.Carrierˣ →* ℂˣ)
  have hσ := rankOneCharacter_isOfWhittakerType p F ψ (Unramified.character F z)
  obtain ⟨ℓ, hℓ⟩ := hσ.exists_ne_zero
  let : Representation.IsIrreducible σ := scalarRepresentation_isIrreducible σ
  let : AddCommGroup (glCoefficientModel ψ 0 σ ℓ).toSubmodule :=
    (glCoefficientModel ψ 0 σ ℓ).toSubmodule.addCommGroup
  let : MeasurableSpace (Langlands.GeneralLinear 1 F.Carrier) := borel _
  let : BorelSpace (Langlands.GeneralLinear 1 F.Carrier) := ⟨rfl⟩
  have hmodel := GodementJacquet.Padic.isMatrixNormalizedGenerator_model_of_pair
    F ψ σ ν hσ hP ℓ hℓ
  have heq := GodementJacquet.matrixRationalValues_equiv
    F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier 0) (glModelEquiv ψ 0 σ ℓ hℓ)
  change IsNormalizedGenerator
    (GodementJacquet.matrixRationalValues F.canonicalTopologicalData.residueCardinality
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier 0) (glModelRepresentation ψ 0 σ ℓ)) P at hmodel
  rw [← heq] at hmodel
  have hvalues := GodementJacquet.Padic.tateMatrixRationalValues_eq_scalar
    F σ (Unramified.character F z) hσ.1.1 (by intro g v; rfl)
  change GodementJacquet.matrixRationalValues
    F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier 0) σ = _ at hvalues
  rw [hvalues] at hmodel
  exact hmodel.unique (unramifiedScalarMellin_isNormalizedGenerator F z)

end Langlands.RankinSelberg
