import Langlands.Global.AdelicRepresentationHeight
import Langlands.Global.AdelicGroupProduct
import Langlands.GroupScheme.Reductive.Basic

/-! # Rational reduction to a compact finite part with polynomial archimedean height -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RepresentationGrowth

/-- For a connected reductive group and a closed matrix representation, every actual adelic
point has a rational left translate whose finite component lies in one fixed compact set and
whose archimedean matrix height is polynomially bounded by the full adelic height of the
point. The compact set, the constant and the exponent do not depend on the point. -/
def AdelicRationalHeightReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {N : ℕ}
    (rho : GroupScheme.MatrixRepresentation G (Fin N)),
    GroupScheme.IsConnectedReductive G → GroupScheme.IsClosedSubgroup rho → 0 < N →
    ∃ (Ω : Set (FiniteAdelicGroupPoints F G)) (C : ℝ) (e : ℕ), IsCompact Ω ∧ 0 < C ∧
      ∀ g : AdelicGroupPoints F G, ∃ q : RationalGroupPoints F G,
        AdelicGroupPoints.finite F G (AdelicGroupPoints.rational F G q * g) ∈ Ω ∧
          height F G rho (AdelicGroupPoints.infinite F G (AdelicGroupPoints.rational F G q * g)) ≤
            C * adelicHeight F G rho g ^ e

end Langlands.Global.RepresentationGrowth
