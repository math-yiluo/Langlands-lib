import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary

/-!
# All-field port of `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeLeibnizFiltrationStatement generalLinearDerivative generalLinearDerivativeLeibnizFiltration_zero generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap leibnizPiece leibnizPiece_obj leibnizPiece_zero leibnizSource leibnizSource_zero mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero
universe uF uV

variable {F : LocalFieldPackage.{uF}}

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

end Langlands.AllFieldBZ.Derivative
