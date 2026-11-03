import Langlands.Global.RepresentationGrowth
import Langlands.GroupScheme.Reductive.Basic

/-! # Polynomial comparison with a closed algebraic embedding height -/

universe u

open AlgebraicGeometry

namespace Langlands.Global.RepresentationGrowth

/-- A scheme-theoretic closed matrix embedding controls the height of every actual
finite-dimensional matrix representation on all infinite adelic points. -/
def ClosedImmersionHeightDominationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (N M : ℕ)
    (rho : GroupScheme.MatrixRepresentation G (Fin N))
    (sigma : GroupScheme.MatrixRepresentation G (Fin M)),
    GroupScheme.IsClosedSubgroup rho →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ d : ℕ, ∀ g : InfiniteAdelicGroupPoints F G,
        height F G sigma g ≤ C * height F G rho g ^ d

end Langlands.Global.RepresentationGrowth
