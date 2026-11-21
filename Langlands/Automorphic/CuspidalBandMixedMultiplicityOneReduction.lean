import Langlands.Automorphic.CuspidalBandMixedMultiplicityOneStatement
import Langlands.Automorphic.OperatorCompactSobolevProof
import Langlands.Global.RankinSelberg.CuspidalBandMixedWhittaker
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerCompletionComparison

/-! # The conditional actual multiplicity-one proof from mixed Whittaker uniqueness -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Automorphic

open Langlands.Global RankinSelbergGlobal RankinSelbergGlobal.ArchimedeanWhittakerRegularity
  CuspidalFixedSmoothDensity OperatorDeterminantSlice NumberField MeasureTheory
  Langlands.Archimedean.MixedSmooth

universe u

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup

/-- Mixed Whittaker uniqueness supplies the original comparison at the band norm. -/
def CuspidalWhittakerBandComparisonFromMixedUniquenessStatement : Prop :=
  CuspidalBandMixedWhittakerUniquenessStatement.{u} →
    CuspidalWhittakerBandSobolevComparisonStatement.{u}

/-- The mixed Whittaker comparison of actual band completions supplies
the original analytic comparison. -/
theorem cuspidalBandComparison_of_mixedUniqueness :
    CuspidalWhittakerBandComparisonFromMixedUniquenessStatement.{u} := by
  intro huniq F _ _ _ r T T' hT hT' e ψ hψ hL2 hL2' hbnd hbnd'
  obtain ⟨χ, hχ, hTχ⟩ := hT
  obtain ⟨χ', hχ', hT'χ'⟩ := hT'
  have hform : ∃ b : T.realization.UnitaryForm, ComputesBandInnerProduct T.realization b :=
    ⟨unitaryForm F (r + 1) T.realization (Nat.succ_ne_zero r) T.cuspidal χ hχ hTχ hL2,
      unitaryForm_inner F (r + 1) T.realization (Nat.succ_ne_zero r) T.cuspidal χ hχ hTχ hL2⟩
  have hform' : ∃ b : T'.realization.UnitaryForm, ComputesBandInnerProduct T'.realization b :=
    ⟨unitaryForm F (r + 1) T'.realization (Nat.succ_ne_zero r) T'.cuspidal χ' hχ' hT'χ' hL2',
      unitaryForm_inner F (r + 1) T'.realization (Nat.succ_ne_zero r) T'.cuspidal χ' hχ' hT'χ' hL2'⟩
  obtain ⟨b, hb⟩ := hform
  obtain ⟨b', hb'⟩ := hform'
  let B := adelicCompletion T χ hχ hTχ b hb
  let B' := adelicCompletion T' χ' hχ' hT'χ' b' hb'
  have hm := hasMixedWhittakerModel_of_bandBound F r T χ hχ hTχ b hb ψ hψ hL2 hbnd
  have hm' := hasMixedWhittakerModel_of_bandBound F r T' χ' hχ' hT'χ' b' hb' ψ hψ hL2' hbnd'
  have h := cuspidalHilbertFullIntertwiner F r T T' χ χ' hχ hχ' hTχ hT'χ' b b' hb hb' e
  obtain ⟨_, E, _, hE, _, hc⟩ := h
  have hline := huniq F r T χ hχ hTχ b hb ψ hψ
  exact exists_proportional_whittaker_of_adelicCompletions T T' b b' B B'
    (bandHasSmoothCoordinateSource T χ hχ hTχ b hb)
    (bandHasSmoothCoordinateSource T' χ' hχ' hT'χ' b' hb')
    ψ e.toIntertwiningMap.toLinearMap E.toContinuousLinearMap hc hE hm hm' hline

/-- With the published Sobolev estimate, the actual mixed uniqueness gives the exact target. -/
theorem cuspidalOperatorMultiplicityOne_of_bandMixed : CuspidalBandMixedUniquenessReductionStatement.{u} :=
  fun huniq => cuspidalWhittakerBandSobolevReduction operatorCompactSobolev
    (cuspidalBandComparison_of_mixedUniqueness huniq)

end Langlands.Automorphic
