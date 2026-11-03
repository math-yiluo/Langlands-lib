import Langlands.GroupScheme.SplitSolvable
import Langlands.GroupScheme.Torus.Split

/-! # Split tori are split solvable over their ground field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A split torus over any field has all the structure and the finite
represented Ga/Gm-series required by the published split-solvable predicate. -/
def SplitTorusSplitSolvableStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : GroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T → IsSplitSolvableGroupScheme T

end Langlands.GroupScheme
