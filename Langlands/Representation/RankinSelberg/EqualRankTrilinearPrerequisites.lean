import Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.RankinSelberg.CentralBilinearVanishingProof
import Langlands.Representation.RankinSelberg.MirabolicBilinearBounds
import Langlands.Representation.Whittaker.MirabolicPairingStatement
import Langlands.Representation.Whittaker.MirabolicFiniteLengthStatement
import Langlands.Representation.Whittaker.CharacterChange
import Langlands.Representation.Classification.FiniteLengthStatement
import Langlands.LocalField.Normalization.Proof

/-! Assembly from the exact representation-theoretic prerequisite statements. -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker InvariantBilinear

universe uF uV uW

/-- The named inputs to equal-rank trilinear uniqueness.
The already-published central bilinear proof is not a missing input. -/
def EqualRankTrilinearPrerequisites
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  GLAdmissibleFiniteLengthStatement.{uF,uV} ∧
  GLAdmissibleFiniteLengthStatement.{uF,uW} ∧
  MirabolicFiniteLengthStatement.{uF,uV} ∧
  MirabolicFiniteLengthStatement.{uF,uW} ∧
  MirabolicFunctionalMultiplicityStatement.{uF,uV} F T n ∧
  MirabolicFunctionalMultiplicityStatement.{uF,uW} F T n ∧
  MirabolicTwistedPairingRigidityStatement.{uF,uV,uW} F T n ∧
  MirabolicCompactTwistedPairingStatement.{uF} F T n ∧
  EqualRankFrobeniusStatement.{uF,uV,uW} F T n

/-- Functional multiplicity and pairing rigidity supply precisely the
irreducible-pair control used in the finite-filtration bound. -/
theorem mirabolic_pair_control_of_statements
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (hmultV : MirabolicFunctionalMultiplicityStatement.{uF,uV} F T n)
    (hmultW : MirabolicFunctionalMultiplicityStatement.{uF,uW} F T n)
    (hrigid : MirabolicTwistedPairingRigidityStatement.{uF,uV,uW} F T n)
    (hcompact : MirabolicCompactTwistedPairingStatement.{uF} F T n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (C : Rep.{uV} ℂ (mirabolic n F.Carrier))
      (D : Rep.{uW} ℂ (mirabolic n F.Carrier)),
      IsSmooth C.ρ → IsSmooth D.ρ →
      Representation.IsIrreducible C.ρ → Representation.IsIrreducible D.ρ →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        (length C.ρ D.ρ
          (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≠ 0 →
          HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier)
            (θ := mirabolicCharacter ψ n) C.ρ ∧
          HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier)
            (θ := mirabolicCharacter ψ n) D.ρ) ∧
        (HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier)
            (θ := mirabolicCharacter ψ n) C.ρ →
          HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier)
            (θ := mirabolicCharacter ψ n) D.ρ →
          length C.ρ D.ρ
            (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≤ 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ C D hC hD hiC hiD
  obtain ⟨E, hE⟩ := hrigid ψ C D C.ρ D.ρ hC hiC hD hiD
  refine ⟨E, ?_⟩
  intro s hs
  let χ := fun g : mirabolic n F.Carrier =>
    determinantWeight (normalizedAbsoluteValue T) g.val (-s)
  have hex (hne : length C.ρ D.ρ χ ≠ 0) :
      Nonempty (C.ρ.Equiv (mirabolicCompactInduced ψ n)) ∧
      Nonempty (D.ρ.Equiv (mirabolicCompactInduced ψ n)) := by
    have hnon : Nontrivial (forms C.ρ D.ρ χ) :=
      not_subsingleton_iff_nontrivial.mp
        (fun hzero => hne (Module.length_eq_zero_iff.mpr hzero))
    let := hnon
    obtain ⟨β, hβ⟩ := exists_ne (0 : forms C.ρ D.ρ χ)
    exact hE s hs β hβ
  constructor
  · intro hne
    obtain ⟨eC, eD⟩ := hex hne
    obtain ⟨lC⟩ := (hmultV ψ C C.ρ hC hiC).2.1.mpr eC
    obtain ⟨lD⟩ := (hmultW ψ D D.ρ hD hiD).2.1.mpr eD
    constructor
    · exact (functionalLength_ne_zero_iff _ _ _).mp (by
        rw [functionalLength_eq_one_of_equiv _ _ _ lC]
        exact one_ne_zero)
    · exact (functionalLength_ne_zero_iff _ _ _).mp (by
        rw [functionalLength_eq_one_of_equiv _ _ _ lD]
        exact one_ne_zero)
  · intro _ _
    by_cases hzero : length C.ρ D.ρ χ = 0
    · rw [hzero]
      exact zero_le
    obtain ⟨⟨eC⟩, ⟨eD⟩⟩ := hex hzero
    obtain ⟨eτ⟩ := hcompact ψ s
    calc
      length C.ρ D.ρ χ =
          length (mirabolicCompactInduced ψ n) D.ρ χ :=
        length_congr_left D.ρ χ eC
      _ = length D.ρ (mirabolicCompactInduced ψ n) χ := length_flip _ _ _
      _ = length (mirabolicCompactInduced ψ n) (mirabolicCompactInduced ψ n) χ :=
        length_congr_left _ χ eD
      _ = 1 := eτ.length_eq.trans (Module.length_eq_one ℂ ℂ)
      _ ≤ 1 := le_rfl

/-- The exact named prerequisite statements imply the unchanged JPSS
equal-rank target. Each input proof remains an explicit premise. -/
theorem equalRankTrilinearUniqueness_of_prerequisites
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (h : EqualRankTrilinearPrerequisites.{uF,uV,uW} F T n) :
    EqualRankTrilinearUniquenessStatement.{uF,uV,uW} F T n := by
  rcases h with ⟨hGLV, hGLW, hresV, hresW, hmultV, hmultW, hrigid, hcompact, hFrob⟩
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply TrilinearReduction.equalRankTrilinearUniqueness_of_source F T n
  dsimp only
  intro ψ V _ _ W _ _ π σ hπ hσ
  obtain ⟨eπ⟩ := hπ.2.2
  obtain ⟨eσinv⟩ := hσ.2.2
  have eσ : functionals (upperUnipotent (n + 1) F.Carrier)
      (standardCharacter ψ n) σ ≃ₗ[ℂ] ℂ := by
    have echange := characterChangeFunctionalEquiv ψ σ (-1)
    have hχ : standardCharacter (ψ.scale (-1)) n = inverseStandardCharacter ψ n :=
      standardCharacter_scale_neg_one ψ n
    simp only [glFunctionals] at echange
    rw [hχ] at echange
    exact echange.trans eσinv
  have hfinπ := hGLV p F (n + 1) (Nat.succ_pos n) V π
    (by rw [← T.topology_eq_canonicalModule]; exact hπ.1) hπ.2.1
  have hfinσ := hGLW p F (n + 1) (Nat.succ_pos n) W σ
    (by rw [← T.topology_eq_canonicalModule]; exact hσ.1) hσ.2.1
  have hmir := mirabolic_exists_exception_length_le_one F T n π σ
    (standardCharacter ψ n) (standardCharacter ψ n) hπ.1.1 hσ.1.1 eπ eσ
    (hresV p F T n V π hπ.1.1 hfinπ) (hresW p F T n W σ hσ.1.1 hfinσ)
    (mirabolic_pair_control_of_statements F T n hmultV hmultW hrigid hcompact ψ)
  exact TrilinearReduction.source_uniqueness_of_mirabolic_bound F T n π σ
    (hFrob V W π σ hπ.1.1 hσ.1.1)
    (mirabolic_shift_length_bound F T n _ _ hmir)
    (centralBilinearVanishing F T n V W π σ hπ.1 hπ.2.1 hσ.1 hσ.2.1)

end Langlands.RankinSelberg
