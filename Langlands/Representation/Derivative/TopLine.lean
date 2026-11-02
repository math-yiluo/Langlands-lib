import Langlands.Representation.Classification.SupercuspidalDerivativesProof

/-!
# A scalar model of a nonzero irreducible top derivative

The input representation need only be irreducible and admissible. Nonvanishing
of its actual top derivative is an explicit hypothesis.
-/

noncomputable section

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis
open Classification.SupercuspidalDerivativesProof

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

private theorem admissible_rankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      IsAdmissible A.representation →
        IsAdmissible ((generalLinearRankCast T h).obj A).representation := by
  let _ := T.topology
  subst b
  exact fun _ hA => hA

private theorem finrank_top (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      A.IsIrreducible → IsAdmissible A.representation →
      Nontrivial ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A) →
        Module.finrank ℂ
          ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A) = 1 := by
  let _ := T.topology
  intro A hirr hadm hD
  have key : ∀ (m : ℕ) (hm : m = 0) (h : n + 1 = m + n + 1),
      Nontrivial ((generalLinearDerivativePositive T ψ m n).obj
        ((generalLinearRankCast T h).obj A)) →
      Module.finrank ℂ ((generalLinearDerivativePositive T ψ m n).obj
        ((generalLinearRankCast T h).obj A)) = 1 := by
    intro m hm h htop
    subst m
    exact finrank_top_of_multiplicityOne T ψ n _
      (multiplicityOne_of_topologicalData T (0 + n) _ ψ _
        (admissible_rankCast T h A hadm)
        (Classification.SupercuspidalTopDerivative.isIrreducible_rankCast T h A hirr))
      htop
  exact key (n + 1 - (n + 1)) (Nat.sub_self _) (rank_eq_of_succ_le le_rfl) hD

/-- An actual linear equivalence from the entire nonzero top derivative of an
admissible irreducible representation of positive rank to the complex scalars.
The choice of equivalence is not asserted to be natural. -/
def topDerivativeLineEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      A.IsIrreducible → IsAdmissible A.representation →
      Nontrivial ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A) →
      ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A) ≃ₗ[ℂ] ℂ := by
  let _ := T.topology
  intro A hirr hadm hD
  let D := (generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A
  have hd : Module.finrank ℂ D = 1 := finrank_top T ψ n A hirr hadm hD
  letI : FiniteDimensional ℂ D := FiniteDimensional.of_finrank_eq_succ hd
  exact LinearEquiv.ofFinrankEq D ℂ (by rw [hd, Module.finrank_self])

end Langlands.Derivative
