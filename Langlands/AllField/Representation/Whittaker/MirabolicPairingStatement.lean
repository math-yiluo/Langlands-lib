import Langlands.Representation.Whittaker.MirabolicPairingStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-!
# Irreducible mirabolic functionals and twisted pairings

Proposition targets for the consequences of JPSS (1983), Proposition 1.4 and
Section 1.5, used in Section 2.10. No classification or proof is asserted here.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MirabolicFunctionalMultiplicityStatement
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV uW

/-- JPSS Section 1.5, Corollary 1: scalar uniqueness of the full character
functional space, recognition of the compact standard representation by a
linear equivalence with `ℂ`, and vanishing for every other irreducible. -/
def MirabolicFunctionalMultiplicityStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ ξ : Representation ℂ (mirabolic n F) V,
      IsSmooth ξ → Representation.IsIrreducible ξ →
      let L := functionals (Mirabolic.upperUnipotent n F)
        (mirabolicCharacter ψ n) ξ
      let τ := mirabolicCompactInduced ψ n
      (∀ ℓ ℓ' : L, ℓ ≠ 0 → ∃ c : ℂ, ℓ' = c • ℓ) ∧
      (Nonempty (L ≃ₗ[ℂ] ℂ) ↔ Nonempty (ξ.Equiv τ)) ∧
      (¬ Nonempty (ξ.Equiv τ) → ∀ ℓ : L, ℓ = 0)

end Langlands.AllField.Whittaker
