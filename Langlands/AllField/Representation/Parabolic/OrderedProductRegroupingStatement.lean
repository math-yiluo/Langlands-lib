import Langlands.Representation.Parabolic.OrderedProductRegroupingStatement
import Langlands.AllField.Representation.Geometric.WeylStatementSupplement
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement
/-! Actual normalized product induction under ordered block refinement. -/

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding OrderedProductRegrouping
open Langlands.AllField.Parabolic

open _root_.CategoryTheory
open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

universe uF uV

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Regroup normalized products along an exact ordered refinement. The input
carrier universe is independent of the field universe. This is a statement. -/
def OrderedProductRegrouping : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B D : BlockShape n) (S : BlockRefinement D)
    (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length)
    (h : ∀ a, (S a.1).size a.2 = B.size (e a)),
    (∀ j k (x : Fin ((S j).size k)),
      D.index j ((S j).index k x) = B.index (e ⟨j,k⟩) (Fin.cast (h ⟨j,k⟩) x)) →
    ∀ σ : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F),
      Nonempty ((T.normalizedProductInductionFunctor.{uF,uV} B).obj σ ≅
        (T.normalizedProductInductionFunctor.{uF,max uF uV} D).obj (fun j =>
          (T.normalizedProductInductionFunctor.{uF,uV} (S j)).obj
            (fun k => (h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩))))

end Langlands.AllField.Parabolic
