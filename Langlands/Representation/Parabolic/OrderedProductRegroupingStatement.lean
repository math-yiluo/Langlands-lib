import Langlands.Representation.Induction.BlockFactors
import Langlands.Group.GL.RefinementCoordinates

/-! Actual normalized product induction under ordered block refinement. -/

namespace Langlands.Parabolic

open CategoryTheory GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Regroup normalized products along an exact ordered refinement. The input
carrier universe is independent of the field universe. This is a statement. -/
def OrderedProductRegrouping : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B D : BlockShape n) (S : BlockRefinement D)
    (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length)
    (h : ∀ a, (S a.1).size a.2 = B.size (e a)),
    (∀ j k (x : Fin ((S j).size k)),
      D.index j ((S j).index k x) = B.index (e ⟨j,k⟩) (Fin.cast (h ⟨j,k⟩) x)) →
    ∀ σ : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      Nonempty ((T.normalizedProductInductionFunctor.{uF,uV} B).obj σ ≅
        (T.normalizedProductInductionFunctor.{uF,max uF uV} D).obj (fun j =>
          (T.normalizedProductInductionFunctor.{uF,uV} (S j)).obj
            (fun k => (h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩))))

end Langlands.Parabolic
