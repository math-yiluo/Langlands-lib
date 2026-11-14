import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.Representation.Derivative.TopLine

/-!
# All-field port of `Langlands.Representation.Derivative.TopLine`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.TopLine` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero topDerivativeLineEquiv
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open Langlands.Classification.SupercuspidalDerivativesProof hiding finrank_generalLinearDerivativePositive_top finrank_generalLinearDerivative_top finrank_top_of_multiplicityOne multiplicityOne_of_topologicalData
open Langlands.AllFieldBZ.Classification.SupercuspidalDerivativesProof
universe uF uV

variable {F : LocalFieldPackage.{uF}}

private theorem _root_.Langlands.Derivative.admissible_rankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      IsAdmissible A.representation →
        IsAdmissible ((generalLinearRankCast T h).obj A).representation := by
  let _ := T.topology
  subst b
  exact fun _ hA => hA

private theorem _root_.Langlands.Derivative.finrank_top (T : F.TopologicalData)
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
    exact Langlands.AllFieldBZ.Classification.SupercuspidalDerivativesProof.finrank_top_of_multiplicityOne T ψ n _
      (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativesProof.multiplicityOne_of_topologicalData T (0 + n) _ ψ _
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

end Langlands.AllFieldBZ.Derivative
