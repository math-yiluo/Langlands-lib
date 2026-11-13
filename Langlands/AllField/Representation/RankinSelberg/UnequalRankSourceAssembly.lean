import Langlands.Representation.RankinSelberg.UnequalRankSourceAssembly
import Langlands.AllField.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearAssembly
import Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankSourceLengthBoundStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankSpecializationInputs
import Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthStatement
import Langlands.AllField.Representation.Whittaker.MirabolicFunctionalMultiplicityProof
/-! Conditional source-length specialization of the separate-group assembly. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.UnequalRankAssembly
open Langlands.RankinSelberg.UnequalRankAssembly hiding character_locallyConstant_of_whittakerType finiteLength_of_whittakerType generalLinear_compactOpen_cofinal mirabolicFunctionalEquivOfWhittakerType mirabolic_smooth_and_character_locallyConstant_of_whittakerType pair_control_of_statements sourceLengthBound_of_statements unequalRankBilinearUniqueness_of_source_length
open Langlands.AllField.RankinSelberg.UnequalRankAssembly
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankMirabolicPairingRigidityStatement UnequalRankSourceLengthBoundStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear hiding UpperUnipotentCompactContainmentStatement upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicCompactMinimalityStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement functionalsCongr mirabolicCompactMinimality mirabolicFunctionalMultiplicity mirabolicFunctionalMultiplicity_canonical mirabolicFunctionalMultiplicity_of_minimality
open Langlands.AllField.Whittaker

universe uF uV uW

/-- The exact rigidity and compact/generic statements supply the pair-control
premise of the mixed finite-length assembly. Both statements remain premises. -/
theorem pair_control_of_statements
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ)
    (hrigid : UnequalRankMirabolicPairingRigidityStatement.{uF,uV,uW} F T n r)
    (hcompact : UnequalRankCompactGenericPairingStatement.{uF,uW} F T n r) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (hnr : n < r) (ψ : UnitaryAdditiveCharacter F)
      (C : Rep.{uV} ℂ (mirabolic r F))
      (D : Rep.{uW} ℂ (Langlands.GeneralLinear (n + 1) F)),
      IsSmooth C.ρ → IsAdmissible D.ρ →
      Representation.IsIrreducible C.ρ → Representation.IsIrreducible D.ρ →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        (MixedBilinear.length (unequalRankMixedLeft hnr) unequalRankMixedRight
            (unequalRankMixedWeight ψ (normalizedAbsoluteValue T) s) C.ρ D.ρ ≠ 0 →
          HasFunctional (N := Mirabolic.upperUnipotent r F)
            (θ := mirabolicCharacter ψ r) C.ρ ∧
          HasFunctional (N := upperUnipotent (n + 1) F)
            (θ := inverseStandardCharacter ψ n) D.ρ) ∧
        (HasFunctional (N := Mirabolic.upperUnipotent r F)
            (θ := mirabolicCharacter ψ r) C.ρ →
          HasFunctional (N := upperUnipotent (n + 1) F)
            (θ := inverseStandardCharacter ψ n) D.ρ →
          MixedBilinear.length (unequalRankMixedLeft hnr) unequalRankMixedRight
            (unequalRankMixedWeight ψ (normalizedAbsoluteValue T) s) C.ρ D.ρ ≤ 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hnr ψ C D hC hD hiC hiD
  obtain ⟨E, hE⟩ := hrigid hnr ψ C D C.ρ D.ρ hC hiC hD hiD
  refine ⟨E, ?_⟩
  intro s hs
  let χ := unequalRankMixedWeight (n := n) (r := r) ψ (normalizedAbsoluteValue T) s
  have hex
      (hne : MixedBilinear.length (unequalRankMixedLeft hnr) unequalRankMixedRight
        χ C.ρ D.ρ ≠ 0) :
      Nonempty (C.ρ.Equiv (mirabolicCompactInduced ψ r)) ∧
        HasFunctional (N := upperUnipotent (n + 1) F)
          (θ := inverseStandardCharacter ψ n) D.ρ := by
    have hsource : Module.length ℂ
        (unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T) C.ρ D.ρ s) ≠ 0 := by
      simpa only [χ, length_unequalRankMixed_eq] using hne
    have hnon : Nontrivial
        (unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T) C.ρ D.ρ s) :=
      not_subsingleton_iff_nontrivial.mp
        (fun hzero => hsource (Module.length_eq_zero_iff.mpr hzero))
    let := hnon
    obtain ⟨B, hB⟩ := exists_ne
      (0 : unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T) C.ρ D.ρ s)
    exact hE s hs B hB
  constructor
  · intro hne
    obtain ⟨⟨eC⟩, hDfun⟩ := hex hne
    let := hiC
    let : Nontrivial C := IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (mirabolic r F)) C.ρ.asModule
    exact ⟨hasFunctional_of_mirabolicCompactEquiv ψ r C.ρ eC, hDfun⟩
  · intro _ _
    by_cases hzero : MixedBilinear.length (unequalRankMixedLeft hnr)
        unequalRankMixedRight χ C.ρ D.ρ = 0
    · rw [hzero]
      exact zero_le
    obtain ⟨⟨eC⟩, hDfun⟩ := hex hzero
    obtain ⟨eτ⟩ := hcompact hnr ψ D D.ρ hD hiD hDfun s
    calc
      MixedBilinear.length (unequalRankMixedLeft hnr) unequalRankMixedRight χ C.ρ D.ρ =
          MixedBilinear.length (unequalRankMixedLeft hnr) unequalRankMixedRight χ
            (mirabolicCompactInduced ψ r) D.ρ :=
        MixedBilinear.length_congr_left unequalRankMixedRight χ D.ρ eC
      _ = Module.length ℂ (unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T)
          (mirabolicCompactInduced ψ r) D.ρ s) :=
        length_unequalRankMixed_eq hnr ψ (normalizedAbsoluteValue T) _ _ s
      _ = 1 := eτ.length_eq.trans (Module.length_eq_one ℂ ℂ)
      _ ≤ 1 := le_rfl

/-- The three exact source statements imply the unchanged source length target.
This compatibility theorem proves none of those three premises. -/
theorem sourceLengthBound_of_statements
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ)
    (hres : MirabolicFiniteLengthStatement.{uF,uV})
    (hrigid : UnequalRankMirabolicPairingRigidityStatement.{uF,uV,uW} F T n r)
    (hcompact : UnequalRankCompactGenericPairingStatement.{uF,uW} F T n r) :
    UnequalRankSourceLengthBoundStatement.{uF,uV,uW} F T n r := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hnr ψ V _ _ W _ _ π σ hπ hσ
  have hP := mirabolic_smooth_and_character_locallyConstant_of_whittakerType
    F T r (standardCharacter ψ r) π hπ
  have hfinπ := finiteLength_of_whittakerType F T r (standardCharacter ψ r) π hπ
  have hfinσ := finiteLength_of_whittakerType F T n (inverseStandardCharacter ψ n) σ hσ
  obtain ⟨E, hE⟩ :=
    MixedBilinear.exists_exception_length_le_one_of_admissibleSecond_finiteLength
      (Mirabolic.upperUnipotent r F)
      (Mirabolic.upperUnipotent_isLimitOfCompactSubgroups F T r)
      (mirabolicCharacter ψ r) hP.2
      (upperUnipotent (n + 1) F)
      (Langlands.AllField.GeneralLinear.upperUnipotent_isLimitOfCompactSubgroups F T (n + 1))
      (inverseStandardCharacter ψ n)
      (character_locallyConstant_of_whittakerType F T n (inverseStandardCharacter ψ n) σ hσ)
      (generalLinear_compactOpen_cofinal F T n)
      (Rep.of (π.comp (mirabolic r F).subtype)) (Rep.of σ)
      (unequalRankMixedLeft hnr) unequalRankMixedRight
      (spectralPoint T.residueCardinality)
      (unequalRankMixedWeight ψ (normalizedAbsoluteValue T))
      hP.1 hσ.1 (hres F T r V π hπ.1.1 hfinπ) hfinσ
      (mirabolicFunctionalEquivOfWhittakerType F T r (standardCharacter ψ r) π hπ)
      (Classical.choice hσ.2.2)
      (pair_control_of_statements F T n r hrigid hcompact hnr ψ)
  refine ⟨E, ?_⟩
  intro s hs
  rw [← length_unequalRankMixed_eq hnr ψ (normalizedAbsoluteValue T)]
  exact hE s hs

end Langlands.AllField.RankinSelberg.UnequalRankAssembly
