import Langlands.Representation.Derivative.LeibnizRankZeroBoundary
import Langlands.Representation.Filtration.OneStep

/-! Complete natural singleton filtrations for the two rank-zero boundaries. -/

noncomputable section
open CategoryTheory

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The actual singleton filtration for a rank-zero first input. -/
def leibnizLeftZeroFiltration (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (b d : ℕ) (hd : d ≤ 0 + b) :
    letI := T.topology
    RepFunctorFiltration (leibnizSource.{uF, uV} T ψ 0 b d hd) 1 := by
  letI := T.topology
  exact RepFunctorFiltration.oneStep _

/-- The sole actual grade is naturally the unique left-zero Leibniz piece. -/
def leibnizLeftZeroGradedIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (b d : ℕ) (hd : d ≤ 0 + b) (x : LeibnizIndex 0 b d) (i : Fin 1) :
    letI := T.topology
    (leibnizLeftZeroFiltration.{uF, uV} T ψ b d hd).graded i ≅
      leibnizPiece T ψ 0 b d x := by
  letI := T.topology
  exact RepFunctorFiltration.oneStepGradedIso _ i ≪≫
    leibnizSourceLeftZeroPieceIso T ψ hd x

/-- Complete feasible-index gluing when the first input has rank zero. -/
theorem generalLinearDerivativeLeibnizFiltration_left_zero (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (b d : ℕ) (hd : d ≤ 0 + b) :
    letI := T.topology
    ∃ e : LeibnizIndex 0 b d ≃ Fin (leibnizIndices 0 b d).card,
      IsGluedFrom (leibnizSource.{uF, uV} T ψ 0 b d hd)
        (fun i => leibnizPiece T ψ 0 b d (e.symm i)) := by
  let _ := T.topology
  let e := (leibnizIndices 0 b d).equivFin
  refine ⟨e, ?_⟩
  apply isGluedFrom_of_length_eq_one (by rw [leibnizIndices_left_zero hd]; simp)
  intro i
  exact leibnizSourceLeftZeroPieceIso T ψ hd (e.symm i)

/-- The actual singleton filtration for a rank-zero second input. -/
def leibnizRightZeroFiltration (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a d : ℕ) (hd : d ≤ a + 0) :
    letI := T.topology
    RepFunctorFiltration (leibnizSource.{uF, uV} T ψ a 0 d hd) 1 := by
  letI := T.topology
  exact RepFunctorFiltration.oneStep _

/-- The sole actual grade is naturally the unique right-zero Leibniz piece. -/
def leibnizRightZeroGradedIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a d : ℕ) (hd : d ≤ a + 0) (x : LeibnizIndex a 0 d) (i : Fin 1) :
    letI := T.topology
    (leibnizRightZeroFiltration.{uF, uV} T ψ a d hd).graded i ≅
      leibnizPiece T ψ a 0 d x := by
  letI := T.topology
  exact RepFunctorFiltration.oneStepGradedIso _ i ≪≫
    leibnizSourceRightZeroPieceIso T ψ hd x

/-- Complete feasible-index gluing when the second input has rank zero. -/
theorem generalLinearDerivativeLeibnizFiltration_right_zero (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a d : ℕ) (hd : d ≤ a + 0) :
    letI := T.topology
    ∃ e : LeibnizIndex a 0 d ≃ Fin (leibnizIndices a 0 d).card,
      IsGluedFrom (leibnizSource.{uF, uV} T ψ a 0 d hd)
        (fun i => leibnizPiece T ψ a 0 d (e.symm i)) := by
  let _ := T.topology
  let e := (leibnizIndices a 0 d).equivFin
  refine ⟨e, ?_⟩
  apply isGluedFrom_of_length_eq_one (by rw [leibnizIndices_right_zero hd]; simp)
  intro i
  exact leibnizSourceRightZeroPieceIso T ψ hd (e.symm i)

end Langlands.Derivative
