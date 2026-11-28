import Langlands.TraceFormula.UnitTwistedOrbitalStatement
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.Analysis.Local.QuotientMass
import Langlands.BaseChange.RegularTransferMeasures

/-!
# The twisted orbital integral of the compact open subgroup indicator

`unitTwistedOrbitalIntegral` proves `UnitTwistedOrbitalIntegralStatement`: under the coset
property, the descended indicator of `K` is the indicator of the image of `K` in the left
quotient by the twisted centralizer, whose mass the compatibility of the quotient measure
computes as `μ(K) / μC(C ∩ K)`. `twistedCoset_of_unitTwistedOrbitalIntegral` is the converse:
that value of the integral forces the coset property.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure Langlands.QuotientIntegration

universe u

section UnitIndicator

variable {G : Type u} [Group G]

/-- The descended indicator of `K` is the indicator of the quotient points whose twisted
conjugate lies in `K`. -/
private theorem unitOrbitFunction_eq_indicator (θ : G →* G) (δ : G) (K : Set G) :
    twistedOrbitFunction θ δ (K.indicator fun _ => (1 : ℂ)) =
      (twistedOrbitFunction θ δ id ⁻¹' K).indicator (fun _ => 1) := by
  funext z
  induction z using Quotient.inductionOn with
  | h x => rfl

variable [TopologicalSpace G]

/-- The image of `K` in the quotient lies in the support of the descended indicator. -/
private theorem compactOpenQuotientOrbit_subset_twistedSupport
    (θ : G →* G) (δ : G) (K : OpenSubgroup G) (hδ : δ ∈ K)
    (hθK : ∀ k ∈ K, θ k ∈ K) :
    compactOpenQuotientOrbit (twistedCentralizer θ δ) K ⊆
      twistedOrbitFunction θ δ id ⁻¹' (K : Set G) := by
  rintro _ ⟨k, hk, rfl⟩
  change k⁻¹ * δ * θ k ∈ K
  exact K.mul_mem (K.mul_mem (K.inv_mem hk) hδ) (hθK k hk)

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- For a closed subgroup `H`, the image of a compact open subgroup `K` in the quotient has
mass `μ(K) / μH(H ∩ K)` for compatible measures. -/
private theorem compactOpenQuotientOrbit_measureReal {H : Subgroup G}
    (hH : IsClosed (H : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (μ : Measure G) (μH : Measure H)
    [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (ν : Measure (LeftQuotient H)) (hν : IsCompatible H μ μH ν) :
    (ν (compactOpenQuotientOrbit H K)).toReal =
      (μ (K : Set G)).toReal / (μH (Subtype.val ⁻¹' (K : Set G))).toReal := by
  let Ω := compactOpenQuotientOrbit H K
  let c := (μH (Subtype.val ⁻¹' (K : Set G))).toReal
  let A := (K : Set G).indicator (fun _ => (1 : ℂ))
  have hcOpen : IsOpen (Subtype.val ⁻¹' (K : Set G) : Set H) :=
    K.isOpen.preimage continuous_subtype_val
  have hcCompact : IsCompact (Subtype.val ⁻¹' (K : Set G) : Set H) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hcpos : 0 < c :=
    ENNReal.toReal_pos (hcOpen.measure_pos μH ⟨1, K.one_mem⟩).ne' hcCompact.measure_lt_top.ne
  have hAclopen : IsClopen (K : Set G) := ⟨K.isClosed, K.isOpen⟩
  have hACont : Continuous A := hAclopen.continuous_indicator continuous_const
  have hASupp : HasCompactSupport A :=
    HasCompactSupport.of_support_subset_isCompact hK Set.support_indicator_subset
  have hav : quotientAverage H μH A = fun z => (c : ℂ) * Ω.indicator (fun _ => 1) z := by
    funext z
    have hz := quotientAverage_compactOpen_leftCoset_indicator H μH K (1 : G) z
    simp only [inv_one, one_mul, mul_one] at hz
    change quotientAverage H μH A z = Ω.indicator (fun _ => (c : ℂ)) z at hz
    rw [hz]
    by_cases h : z ∈ Ω <;> simp [h]
  have hintegral := hν.integral_formula A hACont hASupp
  rw [hav, integral_const_mul,
    integral_indicator_const _ (isOpen_compactOpenQuotientOrbit H K).measurableSet,
    measureReal_def, Complex.real_smul, mul_one] at hintegral
  change (c : ℂ) * ((ν Ω).toReal : ℂ) =
    ∫ g, (K : Set G).indicator (fun _ => (1 : ℂ)) g ∂μ at hintegral
  rw [integral_indicator_const _ K.isOpen.measurableSet, measureReal_def,
    Complex.real_smul, mul_one, ← Complex.ofReal_mul] at hintegral
  exact (eq_div_iff hcpos.ne').mpr ((mul_comm _ _).trans (Complex.ofReal_injective hintegral))

/-- The coset property makes the twisted orbital integral of the subgroup
indicator the ratio of the group and stabilizer masses. -/
theorem unitTwistedOrbitalIntegral : UnitTwistedOrbitalIntegralStatement.{u} := by
  intro G _ _ _ _ _ _ μ _ θ hθ K hKc hKo hθK δ hδ _ _ μC _ _ _ ν hν hcoset
  let C := twistedCentralizer θ δ
  let J : OpenSubgroup G := ⟨K, hKo⟩
  let Ω := compactOpenQuotientOrbit C J
  have horbit : twistedOrbitFunction θ δ id ⁻¹' (K : Set G) = Ω := by
    refine Set.Subset.antisymm (fun z => ?_)
      (compactOpenQuotientOrbit_subset_twistedSupport θ δ J hδ hθK)
    induction z using Quotient.inductionOn with
    | h x =>
      intro hx
      obtain ⟨c, hc, k, hk, rfl⟩ := hcoset x hx
      exact ⟨k, hk, (leftQuotientMap_subgroup_mul C ⟨c, hc⟩ k).symm⟩
  have hΩopen := isOpen_compactOpenQuotientOrbit C J
  have hΩfin := (hν.compactOpenQuotientOrbit_mass J hKc).2.ne
  simp only [twistedOrbitalIntegral, unitOrbitFunction_eq_indicator, horbit]
  refine ⟨(integrable_indicator_iff hΩopen.measurableSet).mpr (integrableOn_const hΩfin), ?_⟩
  rw [integral_indicator_const _ hΩopen.measurableSet, measureReal_def, Complex.real_smul,
    mul_one, compactOpenQuotientOrbit_measureReal (isClosed_twistedCentralizer θ hθ δ) J
      hKc μ μC ν hν]
  rfl

variable [T2Space G]

/-- Converse of `unitTwistedOrbitalIntegral`. Under the hypotheses of
`UnitTwistedOrbitalIntegralStatement` other than the coset property, if the twisted orbital
integral of the characteristic function of `K` equals `μ(K) / μC(C ∩ K)`, then every `x` with
`x⁻¹ * δ * θ x ∈ K` is `c * k` with `c` in the `θ`-centralizer `C` of `δ` and `k ∈ K`. -/
theorem twistedCoset_of_unitTwistedOrbitalIntegral
    (μ : Measure G) [μ.IsHaarMeasure] (θ : G →* G) (hθ : Continuous θ)
    (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hθK : ∀ k ∈ K, θ k ∈ K) (δ : G) (hδ : δ ∈ K)
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]
    (μC : Measure (twistedCentralizer θ δ))
    [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ)))
    (hν : IsCompatible (twistedCentralizer θ δ) μ μC ν)
    (hIntegral : twistedOrbitalIntegral θ δ ν ((K : Set G).indicator fun _ => (1 : ℂ)) =
      (((μ (K : Set G)).toReal / (μC (Subtype.val ⁻¹' (K : Set G))).toReal : ℝ) : ℂ))
    (x : G) (hx : x⁻¹ * δ * θ x ∈ K) :
    ∃ c ∈ twistedCentralizer θ δ, ∃ k ∈ K, x = c * k := by
  let C := twistedCentralizer θ δ
  let J : OpenSubgroup G := ⟨K, hKo⟩
  let q := leftQuotientMap C
  let Ω := compactOpenQuotientOrbit C J
  let S := twistedOrbitFunction θ δ id ⁻¹' (K : Set G)
  have hC := isClosed_twistedCentralizer θ hθ δ
  let := leftQuotient_t2Space C hC
  have hΩclosed := (isCompact_compactOpenQuotientOrbit C J hKc).isClosed
  have hSopen : IsOpen S := by
    have hOrbitContinuous : Continuous (twistedOrbitFunction θ δ id) := by
      apply (leftQuotient_isOpenQuotientMap C).isQuotientMap.continuous_iff.mpr
      exact (continuous_inv.mul continuous_const).mul hθ
    exact hKo.preimage hOrbitContinuous
  have hSub : Ω ⊆ S := compactOpenQuotientOrbit_subset_twistedSupport θ δ J hδ hθK
  have hMass : (ν Ω).toReal =
      (μ (K : Set G)).toReal / (μC (Subtype.val ⁻¹' (K : Set G))).toReal :=
    compactOpenQuotientOrbit_measureReal hC J hKc μ μC ν hν
  obtain ⟨hΩpos, hΩfin⟩ := hν.compactOpenQuotientOrbit_mass J hKc
  rw [twistedOrbitalIntegral, unitOrbitFunction_eq_indicator] at hIntegral
  change (∫ z, S.indicator (fun _ => (1 : ℂ)) z ∂ν) =
    (((μ (K : Set G)).toReal / (μC (Subtype.val ⁻¹' (K : Set G))).toReal : ℝ) : ℂ)
    at hIntegral
  rw [← hMass] at hIntegral
  have hInt : Integrable (S.indicator fun _ => (1 : ℂ)) ν := by
    by_contra h
    rw [integral_undef h] at hIntegral
    exact (Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hΩpos.ne' hΩfin.ne).ne')
      hIntegral.symm
  have hSfin : ν S < ⊤ := by
    have h := (integrable_indicator_iff hSopen.measurableSet).mp hInt
    simpa using (integrableOn_const_iff (by finiteness)).mp h
  rw [integral_indicator_const _ hSopen.measurableSet, measureReal_def,
    Complex.real_smul, mul_one] at hIntegral
  have hEq : ν S = ν Ω :=
    (ENNReal.toReal_eq_toReal_iff' hSfin.ne hΩfin.ne).mp (Complex.ofReal_injective hIntegral)
  have hNull : ν (S \ Ω) = 0 := by
    rw [measure_sdiff hSub hΩclosed.measurableSet.nullMeasurableSet hΩfin.ne, hEq, tsub_self]
  have hqx : q x ∈ S := hx
  have hxΩ : q x ∈ Ω := by
    by_contra h
    let : ν.IsOpenPosMeasure := hν.isOpenPosMeasure
    exact ((hSopen.sdiff hΩclosed).measure_pos ν ⟨q x, hqx, h⟩).ne' hNull
  obtain ⟨k, hk, heq⟩ := hxΩ
  have hc : x * k⁻¹ ∈ C := QuotientGroup.rightRel_apply.mp (Quotient.exact heq)
  exact ⟨x * k⁻¹, hc, k, hk, by simp⟩

end UnitIndicator

end Langlands.TraceFormula
