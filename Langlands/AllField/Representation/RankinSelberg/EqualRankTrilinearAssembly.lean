import Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly
import Langlands.AllField.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement
/-! Conditional assembly for actual row Schwartz functions and coefficient models. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TrilinearReduction
open Langlands.RankinSelberg.TrilinearReduction hiding equalRankTrilinearUniqueness_of_source source_uniqueness_of_mirabolic_bound
open Langlands.AllField.RankinSelberg.TrilinearReduction
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankTrilinearUniquenessStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

section InvariantSpaces

universe uG uS


end InvariantSpaces

section Field


end Field

/-- The actual row-action reduction, with its two finite exceptional sets and
its weight-shifted Frobenius equivalence left as explicit mathematical inputs. -/
theorem source_uniqueness_of_mirabolic_bound
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (∀ s : ℂ, Nonempty
      (invariantForms (S := (rowVanishingAtZero (F := F) (n := n + 1)).toSubmodule)
        ρ σ (rowVanishingAtZero (F := F) (n := n + 1)).toRepresentation
        (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) ≃ₗ[ℂ]
      InvariantBilinear.forms (ρ.comp (mirabolic n F).subtype)
        (σ.comp (mirabolic n F).subtype)
        (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (1 - s)))) →
    (∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      InvariantBilinear.length (ρ.comp (mirabolic n F).subtype)
        (σ.comp (mirabolic n F).subtype)
        (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (1 - s)) ≤ 1) →
    (∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      ∀ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ,
        (∀ g v w, β (ρ g v) (σ g w) =
          determinantWeight (normalizedAbsoluteValue T) g (-s) * β v w) → β = 0) →
    ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      ∀ B B' : Form (V := V) (W := W)
        (S := SchwartzBruhat (Fin (n + 1) → F)),
        Invariant ρ σ rowSchwartzRepresentation
          (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) B →
        Invariant ρ σ rowSchwartzRepresentation
          (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) B' →
        B ≠ 0 → ∃ c : ℂ, B' = c • B := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hFrob hmir hbil
  apply uniqueness_outside_finite_union ρ σ rowSchwartzRepresentation
    (fun s g => determinantWeight (normalizedAbsoluteValue T) g (-s))
    rowEvaluationAtZero (fun g φ => rowEvaluationAtZero_translate g φ)
    (spectralPoint T.residueCardinality) hbil
  obtain ⟨E, hE⟩ := hmir
  refine ⟨E, ?_⟩
  intro s hs B B' hB hB' hB0
  obtain ⟨e⟩ := hFrob s
  exact restriction_uniqueness_of_bilinear_equiv ρ σ _ _ e (hE s hs) B B' hB hB' hB0

/-- The parent target follows from a uniform source-carrier uniqueness bound.
The bound is an outstanding representation-theoretic input, not a proved fact. -/
theorem equalRankTrilinearUniqueness_of_source
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (hsource :
      let := T.topology
      let := T.valuativeRel
      let := T.localField
      ∀ (ψ : UnitaryAdditiveCharacter F)
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
          ∀ B B' : Form (V := V) (W := W)
            (S := SchwartzBruhat (Fin (n + 1) → F)),
            Invariant π σ rowSchwartzRepresentation
              (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) B →
            Invariant π σ rowSchwartzRepresentation
              (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) B' →
            B ≠ 0 → ∃ c : ℂ, B' = c • B) :
    EqualRankTrilinearUniquenessStatement.{uF,uV,uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ W _ _ π σ hπ hσ ℓ ℓ'
  obtain ⟨E, hE⟩ := hsource ψ V W π σ hπ hσ
  refine ⟨E, ?_⟩
  intro s hs B B' hB hB' hB0
  exact coefficientModel_uniqueness_of_source π σ ℓ ℓ'
    (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s))
    (hE s hs) B B' hB hB' hB0

end Langlands.AllField.RankinSelberg.TrilinearReduction
