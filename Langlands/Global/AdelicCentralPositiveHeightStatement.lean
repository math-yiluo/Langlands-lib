import Langlands.Global.AdelicRepresentationHeight
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.AdelicGroupNormOne
import Langlands.GroupScheme.Reductive.Basic

/-! # Central archimedean factors of adelic points with polynomially bounded height -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RepresentationGrowth

/-- For a connected reductive group and a closed matrix representation, every actual adelic
point is a central point with trivial finite component times a norm-one point, and the
central factor can be chosen with full adelic height polynomially bounded by that of the
point. -/
def CentralNormOneHeightFactorStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {N : ℕ}
    (rho : GroupScheme.MatrixRepresentation G (Fin N)),
    GroupScheme.IsConnectedReductive G → GroupScheme.IsClosedSubgroup rho → 0 < N →
    ∃ (c : ℝ) (e : ℕ), ∀ g : AdelicGroupPoints F G, ∃ z : AdelicGroupPoints F G,
      (∀ x : AdelicGroupPoints F G, Commute z x) ∧
        AdelicGroupPoints.finite F G z = 1 ∧
        z⁻¹ * g ∈ AdelicGroupPoints.normOneSubgroup F G ∧
        adelicHeight F G rho z ≤ c * adelicHeight F G rho g ^ e

end Langlands.Global.RepresentationGrowth
