import Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement
import Langlands.AllField.Representation.RankinSelberg.EqualRankTrilinearAssembly
/-!
# Frobenius equivalence on actual row Schwartz functions vanishing at zero

The equivalence in JPSS (2.10.5)--(2.10.6) is stated for arbitrary smooth
representations. Its construction and proof remain separate obligations.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankTrilinearUniquenessStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.GeneralLinear
open Langlands.RankinSelberg.TrilinearReduction hiding equalRankTrilinearUniqueness_of_source source_uniqueness_of_mirabolic_bound
open Langlands.AllField.RankinSelberg.TrilinearReduction

universe uF uV uW

/-- The full twisted invariant trilinear space on actual row test functions
vanishing at zero is complex-linearly equivalent to the actual mirabolic
bilinear space with the modularly shifted covariance `|det p|^(1-s)`. -/
def EqualRankFrobeniusStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsSmooth ρ → IsSmooth σ →
      ∀ s : ℂ, Nonempty
        (invariantForms
          (S := (rowVanishingAtZero (F := F) (n := n + 1)).toSubmodule)
          ρ σ (rowVanishingAtZero (F := F) (n := n + 1)).toRepresentation
          (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) ≃ₗ[ℂ]
        InvariantBilinear.forms (ρ.comp (mirabolic n F).subtype)
          (σ.comp (mirabolic n F).subtype)
          (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (1 - s)))

end Langlands.AllField.RankinSelberg
