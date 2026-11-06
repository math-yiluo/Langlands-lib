import Langlands.Global.AdelicRepresentationHeight
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-! # Continuity and properness of full adelic representation heights -/

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RepresentationGrowth

/-- The existing positive-rank full adelic height is continuous for every
representation, and is a proper map when the representation is a closed immersion. -/
def AdelicRepresentationHeightPropernessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (N : ℕ) (rho : GroupScheme.MatrixRepresentation G (Fin N)),
    0 < N →
      Continuous (adelicHeight F G rho) ∧
      (GroupScheme.IsClosedSubgroup rho → IsProperMap (adelicHeight F G rho))

end Langlands.Global.RepresentationGrowth
