import Langlands.Global.AdelicRepresentationHeight
import Langlands.GroupScheme.Reductive.Basic

/-! # Polynomial domination of full adelic representation heights -/

universe u

open AlgebraicGeometry

namespace Langlands.Global.RepresentationGrowth

/-- A closed matrix embedding of positive rank controls every positive-rank
matrix representation on all actual full adelic points, with one constant and
one natural exponent chosen before the point. -/
def ClosedImmersionAdelicHeightDominationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (N M : ℕ)
    (rho : GroupScheme.MatrixRepresentation G (Fin N))
    (sigma : GroupScheme.MatrixRepresentation G (Fin M)),
    0 < N → 0 < M → GroupScheme.IsClosedSubgroup rho →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ e : ℕ, ∀ g : AdelicGroupPoints F G,
        adelicHeight F G sigma g ≤ C * adelicHeight F G rho g ^ e

end Langlands.Global.RepresentationGrowth
