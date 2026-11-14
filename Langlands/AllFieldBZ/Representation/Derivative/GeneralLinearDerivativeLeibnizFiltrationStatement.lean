import Langlands.AllFieldBZ.Representation.Derivative.Iteration
import Langlands.AllFieldBZ.Representation.Induction.BinaryProduct
import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement

/-!
# All-field port of `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeLeibnizFiltrationStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap leibnizPiece leibnizPiece_obj leibnizSource mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-- The literal derivative of the actual binary normalized product, viewed in `Rep`. -/
def leibnizSource (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (hd : d ≤ a + b) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier) := by
  letI := T.topology
  exact T.binaryNormalizedProductFunctor a b ⋙
    generalLinearDerivative T ψ (a + b) d hd ⋙ SmoothRep.toRep

/-- A feasible grade: derivative of each factor, binary product, smooth rank cast,
then the forgetful functor to `Rep`. -/
def leibnizPiece (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (x : LeibnizIndex a b d) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier) := by
  letI := T.topology
  exact (generalLinearDerivative T ψ a x.val.1 (leibnizIndices_left_le x.property)).prod
      (generalLinearDerivative T ψ b x.val.2 (leibnizIndices_right_le x.property)) ⋙
    T.binaryNormalizedProductFunctor (a - x.val.1) (b - x.val.2) ⋙
    generalLinearRankCast T (leibnizIndices_rank x.property) ⋙ SmoothRep.toRep

theorem leibnizPiece_obj (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (x : LeibnizIndex a b d) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      (leibnizPiece T ψ a b d x).obj (A, B) =
        SmoothRep.toRep.obj
          ((generalLinearRankCast T (leibnizIndices_rank x.property)).obj
            ((T.binaryNormalizedProductFunctor (a - x.val.1) (b - x.val.2)).obj
              ((generalLinearDerivative T ψ a x.val.1
                  (leibnizIndices_left_le x.property)).obj A,
                (generalLinearDerivative T ψ b x.val.2
                  (leibnizIndices_right_le x.property)).obj B))) := by
  intros
  rfl

variable (F) in
/-- BZ77 4.14(c) as an actual natural filtration, with every feasible index exactly
once and arbitrary ordering, including all rank-zero and top-order boundaries. -/
def GeneralLinearDerivativeLeibnizFiltrationStatement (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (hd : d ≤ a + b),
    ∃ e : LeibnizIndex a b d ≃ Fin (leibnizIndices a b d).card,
      IsGluedFrom (leibnizSource.{uF, uV} T ψ a b d hd)
        (fun i => leibnizPiece T ψ a b d (e.symm i))

/-- Extract a genuine filtration; absorb the gluing permutation into its enumeration.
This is a consequence of a supplied Leibniz assertion, not a proof of that assertion. -/
theorem GeneralLinearDerivativeLeibnizFiltrationStatement.filtration
    (T : F.TopologicalData)
    (h : GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (hd : d ≤ a + b) :
    letI := T.topology
    ∃ e : LeibnizIndex a b d ≃ Fin (leibnizIndices a b d).card,
      ∃ s : RepFunctorFiltration (leibnizSource.{uF, uV} T ψ a b d hd)
          (leibnizIndices a b d).card,
        ∀ i, Nonempty (s.graded i ≅ leibnizPiece T ψ a b d (e.symm i)) := by
  let _ := T.topology
  obtain ⟨e, σ, s, hs⟩ := h ψ a b d hd
  exact ⟨e.trans σ.symm, s, hs⟩

end Langlands.AllFieldBZ.Derivative
