import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# The actual irreducible generic socle of a Whittaker coefficient model

This closed proposition records the minimal invariant subspace used in JPSS
(1983), Section 5.4, printed page 423, with the full Whittaker-type hypotheses
of Section 2.1. It is a statement, not a proof.
-/

namespace Langlands.Whittaker

open HarmonicAnalysis

universe uF uV

/-- Every nonzero-functional coefficient image of a representation of Whittaker
 type has a nonzero irreducible subrepresentation contained in every nonzero
 subrepresentation, and that inherited representation is itself of full
 Whittaker type. The original representation may be reducible. -/
def ModelGenericSocleStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
      RankinSelberg.IsOfWhittakerType n (standardCharacter ψ n) σ →
      ∀ ℓ : glFunctionals ψ n σ, ℓ.val ≠ 0 →
        letI : AddCommGroup (glCoefficientModel ψ n σ ℓ).toSubmodule :=
          (glCoefficientModel ψ n σ ℓ).toSubmodule.addCommGroup
        let M := glModelRepresentation ψ n σ ℓ
        ∃ S : Subrepresentation M,
          S ≠ ⊥ ∧
          Representation.IsIrreducible (V := S.toSubmodule) S.toRepresentation ∧
          (∀ T : Subrepresentation M, T ≠ ⊥ → S ≤ T) ∧
          RankinSelberg.IsOfWhittakerType (V := S.toSubmodule)
            n (standardCharacter ψ n) S.toRepresentation

end Langlands.Whittaker
