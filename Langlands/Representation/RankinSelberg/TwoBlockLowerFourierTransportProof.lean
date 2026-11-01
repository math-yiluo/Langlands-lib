import Langlands.Representation.RankinSelberg.TwoBlockLowerFourierAnalytic

/-! # Actual lower quotient Fourier and coefficient transport -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  TwoBlockLowerUnipotentQuotient TwoBlockLowerUnfolding TwoBlockLowerFourier

universe uF uW

/-- The actual lower Fourier comparison, with the supplied compatible measures
and only the published scalar-section assembly premise. -/
theorem twoBlockLowerFourierTransport :
    TwoBlockLowerFourierTransportStatement.{uF,uW} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro t m h mD hD
  let := T.generalLinearTopologicalGroup (t + 1)
  intro G N NQ HQ HQD
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace NQ := borel NQ
  let : BorelSpace NQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace HQD := borel HQD
  let : BorelSpace HQD := ⟨rfl⟩
  intro Tdual
  refine ⟨lowerDuality F.Carrier h, lowerDuality_mk F.Carrier h,
    lowerDuality_symm_mk F.Carrier h, lowerDuality_order F h,
    lowerDuality_symm_order F h, lowerDuality_slices F h, ?_, ?_, ?_⟩
  · intro g
    rw [lowerDuality_conjugation, standardDuality_mk]
  · exact lowerDuality_measure_transport F h
  · intro ψ ψD Wtest
    refine ⟨firstDualFunction ψ t Wtest, firstDualFunction_apply ψ t Wtest,
      lowerDualTest_rotation h ψ Wtest, ?_⟩
    intro ν hsd Φ Φhat hpair
    have hpartial := partialSection_fourier F h ψ ν hsd Φ Φhat hpair
    refine ⟨hpartial, ?_⟩
    intro W hAdd hMod σ ell WD σD ellD f fD hscalar E ED
    have hgroup (g : G) :
        groupIntegrand ellD fD (firstDualFunction ψ t Wtest) Φhat ν (Tdual g) =
          (T.normalizedAbs (determinant g : F.Carrier) : ℂ) *
            groupIntegrand ell f Wtest Φ ν g := by
      rw [groupIntegrand_def, groupIntegrand_def,
        lowerDualTest_rotation h ψ Wtest, hscalar g, hpartial g]
      ring
    have hquot (z : HQ) :
        ED (lowerDuality F.Carrier h z) =
          (((T.residueCardinality : ℝ) ^
              (-TwoBlockLowerUnipotentQuotient.determinantOrder F h z) : ℝ) : ℂ) * E z := by
      induction z using Quotient.inductionOn with
      | h g =>
        change integrand ellD fD (firstDualFunction ψ t Wtest) Φhat ν
            (lowerDuality F.Carrier h (Quotient.mk _ g)) = _
        rw [lowerDuality_mk, integrand_mk_eq_groupIntegrand]
        change groupIntegrand ellD fD (firstDualFunction ψ t Wtest) Φhat ν (Tdual g) = _
        rw [hgroup]
        change (T.normalizedAbs (determinant g : F.Carrier) : ℂ) *
            groupIntegrand ell f Wtest Φ ν g =
          (((T.residueCardinality : ℝ) ^
              (-TwoBlockLowerUnipotentQuotient.determinantOrder F h (Quotient.mk _ g)) : ℝ) : ℂ) *
            groupIntegrand ell f Wtest Φ ν g
        rw [TwoBlockLowerUnipotentQuotient.determinantOrder_mk,
          T.normalizedAbs_of_ne_zero (determinant g).ne_zero]
    refine ⟨hgroup, hquot, ?_⟩
    intro μG μN hN
    let := hN
    intro νN hνN νMinus νMinusD k
    have hm := lowerDuality_measure_transport F h hN νN hνN
    have hDslice : MeasurePreserving (lowerDuality F.Carrier h)
        (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k))
        (νMinusD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F hD (-k))) :=
      ⟨(lowerDuality F.Carrier h).continuous.measurable, (hm.2.2 k).1⟩
    have hE : ∀ᵐ z ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k),
        ED (lowerDuality F.Carrier h z) =
          (((T.residueCardinality : ℝ) ^ (-k) : ℝ) : ℂ) * E z := by
      filter_upwards [ae_restrict_mem
        (TwoBlockLowerUnipotentQuotient.isClopen_determinantSlice F h k).1.measurableSet] with z hz
      have hk := (TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder F h).mp hz
      simpa only [hk] using hquot z
    have hq : 0 < (T.residueCardinality : ℝ) := by
      exact_mod_cast Nat.zero_lt_one.trans T.residueCardinality_gt_one
    have hs := scalar_transport (lowerDuality F.Carrier h).toMeasurableEquiv
      hDslice E ED ((T.residueCardinality : ℝ) ^ (-k)) (zpow_pos hq _) hE
    have hcast : (((T.residueCardinality : ℝ) ^ (-k) : ℝ) : ℂ) =
        (T.residueCardinality : ℂ) ^ (-k) := by
      simp only [Complex.ofReal_zpow, Complex.ofReal_natCast]
    simpa only [hcast] using hs

end Langlands.RankinSelberg
