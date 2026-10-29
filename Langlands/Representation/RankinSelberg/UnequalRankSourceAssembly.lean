import Langlands.Representation.RankinSelberg.UnequalRankSourceLengthBoundStatement
import Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement
import Langlands.Representation.RankinSelberg.UnequalRankMixedAdapter
import Langlands.Representation.RankinSelberg.UnequalRankSpecializationInputs
import Langlands.Representation.RankinSelberg.UnequalRankBilinearAssembly
import Langlands.Representation.Whittaker.MixedFunctionalBilinearBoundsProof
import Langlands.Representation.Whittaker.MirabolicCompactFunctional
import Langlands.Representation.Whittaker.MirabolicFiniteLengthStatement

/-! Conditional source-length specialization of the separate-group assembly. -/

noncomputable section

namespace Langlands.RankinSelberg.UnequalRankAssembly

open GeneralLinear HarmonicAnalysis Whittaker

universe uF uV uW

/-- The three exact source inputs to the unequal-rank assembly.
This proposition only packages the inputs; it asserts none of them. -/
def SourcePrerequisites
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    Prop :=
  MirabolicFiniteLengthStatement.{uF,uV} ∧
  UnequalRankMirabolicPairingRigidityStatement.{uF,uV,uW} F T n r ∧
  UnequalRankCompactGenericPairingStatement.{uF,uW} F T n r

/-- The exact rigidity and compact/generic statements supply the pair-control
premise of the mixed finite-length assembly. Both statements remain premises. -/
theorem pair_control_of_statements
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ)
    (hrigid : UnequalRankMirabolicPairingRigidityStatement.{uF,uV,uW} F T n r)
    (hcompact : UnequalRankCompactGenericPairingStatement.{uF,uW} F T n r) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (hnr : n < r) (ψ : UnitaryAdditiveCharacter F.Carrier)
      (C : Rep.{uV} ℂ (mirabolic r F.Carrier))
      (D : Rep.{uW} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier)),
      IsSmooth C.ρ → IsAdmissible D.ρ →
      Representation.IsIrreducible C.ρ → Representation.IsIrreducible D.ρ →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        (MixedBilinear.length (unequalRankMixedLeft hnr) unequalRankMixedRight
            (unequalRankMixedWeight ψ (normalizedAbsoluteValue T) s) C.ρ D.ρ ≠ 0 →
          HasFunctional (N := Mirabolic.upperUnipotent r F.Carrier)
            (θ := mirabolicCharacter ψ r) C.ρ ∧
          HasFunctional (N := upperUnipotent (n + 1) F.Carrier)
            (θ := inverseStandardCharacter ψ n) D.ρ) ∧
        (HasFunctional (N := Mirabolic.upperUnipotent r F.Carrier)
            (θ := mirabolicCharacter ψ r) C.ρ →
          HasFunctional (N := upperUnipotent (n + 1) F.Carrier)
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
        HasFunctional (N := upperUnipotent (n + 1) F.Carrier)
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
      (MonoidAlgebra ℂ (mirabolic r F.Carrier)) C.ρ.asModule
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
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ)
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
      (Mirabolic.upperUnipotent r F.Carrier)
      (Mirabolic.upperUnipotent_isLimitOfCompactSubgroups F T r)
      (mirabolicCharacter ψ r) hP.2
      (upperUnipotent (n + 1) F.Carrier)
      (GeneralLinear.upperUnipotent_isLimitOfCompactSubgroups F T (n + 1))
      (inverseStandardCharacter ψ n)
      (character_locallyConstant_of_whittakerType F T n (inverseStandardCharacter ψ n) σ hσ)
      (generalLinear_compactOpen_cofinal F T n)
      (Rep.of (π.comp (mirabolic r F.Carrier).subtype)) (Rep.of σ)
      (unequalRankMixedLeft hnr) unequalRankMixedRight
      (spectralPoint T.residueCardinality)
      (unequalRankMixedWeight ψ (normalizedAbsoluteValue T))
      hP.1 hσ.1 (hres p F T r V π hπ.1.1 hfinπ) hfinσ
      (mirabolicFunctionalEquivOfWhittakerType F T r (standardCharacter ψ r) π hπ)
      (Classical.choice hσ.2.2)
      (pair_control_of_statements F T n r hrigid hcompact hnr ψ)
  refine ⟨E, ?_⟩
  intro s hs
  rw [← length_unequalRankMixed_eq hnr ψ (normalizedAbsoluteValue T)]
  exact hE s hs

/-- The same three source premises imply full unequal-rank uniqueness through
the published source-carrier descent; no premise is discharged here. -/
theorem unequalRankBilinearUniqueness_of_statements
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ)
    (hres : MirabolicFiniteLengthStatement.{uF,uV})
    (hrigid : UnequalRankMirabolicPairingRigidityStatement.{uF,uV,uW} F T n r)
    (hcompact : UnequalRankCompactGenericPairingStatement.{uF,uW} F T n r) :
    UnequalRankBilinearUniquenessStatement.{uF,uV,uW} F T n r :=
  unequalRankBilinearUniqueness_of_source_length F T n r
    (sourceLengthBound_of_statements F T n r hres hrigid hcompact)

/-- The named prerequisite bundle supplies the unchanged source length target. -/
theorem sourceLengthBound_of_prerequisites
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ)
    (h : SourcePrerequisites.{uF,uV,uW} F T n r) :
    UnequalRankSourceLengthBoundStatement.{uF,uV,uW} F T n r :=
  sourceLengthBound_of_statements F T n r h.1 h.2.1 h.2.2

/-- The named prerequisite bundle supplies conditional full uniqueness. -/
theorem unequalRankBilinearUniqueness_of_prerequisites
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ)
    (h : SourcePrerequisites.{uF,uV,uW} F T n r) :
    UnequalRankBilinearUniquenessStatement.{uF,uV,uW} F T n r :=
  unequalRankBilinearUniqueness_of_statements F T n r h.1 h.2.1 h.2.2

end Langlands.RankinSelberg.UnequalRankAssembly
