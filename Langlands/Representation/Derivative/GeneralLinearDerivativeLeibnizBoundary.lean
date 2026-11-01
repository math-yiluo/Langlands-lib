import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
import Langlands.Representation.Filtration.OneStep

/-! The actual order-zero boundary of the general linear Leibniz filtration. -/

noncomputable section
open CategoryTheory

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- At order zero the literal source is the actual binary product followed by forgetting. -/
theorem leibnizSource_zero (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b : ℕ) (hd : 0 ≤ a + b) :
    letI := T.topology
    leibnizSource.{uF, uV} T ψ a b 0 hd =
      T.binaryNormalizedProductFunctor a b ⋙ SmoothRep.toRep := by
  let _ := T.topology
  simp only [leibnizSource, generalLinearDerivative_zero, Functor.id_comp]
  rfl

/-- Each feasible order-zero piece is the same actual binary product functor. -/
theorem leibnizPiece_zero (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b : ℕ) (x : LeibnizIndex a b 0) :
    letI := T.topology
    leibnizPiece.{uF, uV} T ψ a b 0 x =
      T.binaryNormalizedProductFunctor a b ⋙ SmoothRep.toRep := by
  let _ := T.topology
  have hx : x.val = (0, 0) := by
    simpa only [leibnizIndices_zero, Finset.mem_singleton] using x.property
  rcases x with ⟨x, hxmem⟩
  dsimp only at hx
  subst x
  simp only [leibnizPiece, generalLinearDerivative_zero, Nat.sub_zero,
    generalLinearRankCast_refl]
  rfl

/-- A concrete natural filtration of the literal order-zero source. -/
def leibnizZeroFiltration (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b : ℕ) (hd : 0 ≤ a + b) :
    letI := T.topology
    RepFunctorFiltration (leibnizSource.{uF, uV} T ψ a b 0 hd) 1 := by
  letI := T.topology
  exact RepFunctorFiltration.oneStep _

/-- Every order-zero feasible piece identifies naturally with the sole actual grade. -/
def leibnizZeroGradedIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b : ℕ) (hd : 0 ≤ a + b) (x : LeibnizIndex a b 0) (i : Fin 1) :
    letI := T.topology
    (leibnizZeroFiltration.{uF, uV} T ψ a b hd).graded i ≅
      leibnizPiece T ψ a b 0 x := by
  letI := T.topology
  exact RepFunctorFiltration.oneStepGradedIso _ i ≪≫
    eqToIso ((leibnizSource_zero T ψ a b hd).trans (leibnizPiece_zero T ψ a b x).symm)

/-- The order-zero case of the unchanged all-rank Leibniz assertion. -/
theorem generalLinearDerivativeLeibnizFiltration_zero (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b : ℕ) (hd : 0 ≤ a + b) :
    letI := T.topology
    ∃ e : LeibnizIndex a b 0 ≃ Fin (leibnizIndices a b 0).card,
      IsGluedFrom (leibnizSource.{uF, uV} T ψ a b 0 hd)
        (fun i => leibnizPiece T ψ a b 0 (e.symm i)) := by
  let _ := T.topology
  let e := (leibnizIndices a b 0).equivFin
  refine ⟨e, ?_⟩
  apply isGluedFrom_of_length_eq_one (by simp)
  intro i
  exact eqToIso ((leibnizSource_zero T ψ a b hd).trans
    (leibnizPiece_zero T ψ a b (e.symm i)).symm)

end Langlands.Derivative
