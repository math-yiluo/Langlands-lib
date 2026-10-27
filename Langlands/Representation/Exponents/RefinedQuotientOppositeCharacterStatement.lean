import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Parabolic.OppositeRefinementFunctors

/-!
# Scalar characters of upper refined quotients occur in opposite Jacquet modules

If an admissible representation `σ` of the common refined Levi, on which the
flattened block scalars act through a character `χ`, has an actual nonzero
admissible quotient of its upper normalized refined induction, then `χ` has
open kernel and is a generalized eigencharacter of the normalized opposite
Jacquet module of that quotient, restricted along the same scalar map.
This is a statement.
-/

namespace Langlands.Exponents

open GeneralLinear Geometric

universe uF uV uW

/-- A whole-source scalar character of an admissible `σ` occurs in the actual
normalized opposite Jacquet module of every nontrivial admissible quotient of
the actual upper normalized refined induction of `σ`. -/
def RefinedQuotientOppositeCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
      (π : Rep.{uW} ℂ (B.Levi F.Carrier)),
      IsAdmissible σ.ρ → IsAdmissible π.ρ → Nontrivial π.V →
      ∀ (χ : (Fin (B.flatten S).length → F.Carrierˣ) →* ℂˣ),
        let z : (Fin (B.flatten S).length → F.Carrierˣ) →* refinedLevi F.Carrier B S :=
          (flattenedLeviEquiv F.Carrier B S).toMonoidHom.comp
            ((B.flatten S).blockScalarLevi F.Carrier)
        Classification.HasScalarCharacter σ.ρ z χ →
        (∃ q : (T.normalizedRefinedInduced B S σ.ρ).IntertwiningMap π.ρ,
          Function.Surjective q) →
        IsOpen (χ.ker : Set (Fin (B.flatten S).length → F.Carrierˣ)) ∧
          IsGeneralizedEigencharacter
            ((T.normalizedRefinedOppositeJacquet B S π.ρ).comp z) χ

end Langlands.Exponents
