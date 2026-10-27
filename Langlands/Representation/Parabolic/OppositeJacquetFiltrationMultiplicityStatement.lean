import Langlands.Representation.Parabolic.OppositeJacquetFiltration
import Langlands.Representation.Filtration.MultiplicityStatement

/-! Actual finite-series multiplicity additivity and decomposition for
normalized opposite Jacquet functors. These are proposition definitions. -/

open scoped BigOperators

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Multiplicities in the actual inner opposite quotient are precisely sums
of actual finite-series multiplicities in the original graded quotients. -/
def NormalizedRefinedOppositeJacquetFiltrationMultiplicityClause : Prop :=
  letI := T.topology
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V),
    IsSmooth ρ →
      ∀ (l : ℕ) (s : ObjectRepFiltration (Rep.of ρ) l)
        (τ : Rep.{uW} ℂ (refinedLevi F.Carrier B S)) (m : ℕ),
        HasJordanHolderMultiplicity
            (Rep.of (T.normalizedRefinedOppositeJacquet B S ρ)) τ m ↔
          ∃ counts : Fin l → ℕ,
            (∀ i : Fin l, HasJordanHolderMultiplicity
              (Rep.of (T.normalizedRefinedOppositeJacquet B S
                (s.gradedRepresentation i).ρ)) τ (counts i)) ∧
            (∑ i : Fin l, counts i) = m

/-- The same constructive multiplicity criterion for the actual composed
opposite quotient of an ambient general-linear representation. -/
def NormalizedComposedOppositeJacquetFiltrationMultiplicityClause : Prop :=
  letI := T.topology
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
    IsSmooth ρ →
      ∀ (l : ℕ) (s : ObjectRepFiltration (Rep.of ρ) l)
        (τ : Rep.{uW} ℂ (refinedLevi F.Carrier B S)) (m : ℕ),
        HasJordanHolderMultiplicity
            (Rep.of (T.normalizedComposedOppositeJacquet B S ρ)) τ m ↔
          ∃ counts : Fin l → ℕ,
            (∀ i : Fin l, HasJordanHolderMultiplicity
              (Rep.of (T.normalizedComposedOppositeJacquet B S
                (s.gradedRepresentation i).ρ)) τ (counts i)) ∧
            (∑ i : Fin l, counts i) = m

/-- Both finite-filtration criteria, with independent field, input-carrier
and constituent-carrier universes. -/
def NormalizedOppositeJacquetFiltrationMultiplicityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (S : BlockRefinement B),
    NormalizedRefinedOppositeJacquetFiltrationMultiplicityClause.{uF, uV, uW}
        F T B S ∧
    NormalizedComposedOppositeJacquetFiltrationMultiplicityClause.{uF, uV, uW}
        F T B S

end Langlands.Parabolic
