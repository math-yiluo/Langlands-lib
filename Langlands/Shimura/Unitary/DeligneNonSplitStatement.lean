import Langlands.GroupScheme.Torus.Split
import Langlands.Shimura.Unitary.DeligneSchemeSplitting

/-! # The real Deligne torus is a non-split torus -/

open AlgebraicGeometry

namespace Langlands.Shimura.DeligneTorus

/-- The real Deligne group scheme is smooth over `Spec ℝ`, its pullback to `Spec ℂ` is a split
torus, and it is not itself a split torus over `Spec ℝ`. -/
def NonSplitTorusStatement : Prop :=
  Smooth groupScheme.X.hom ∧ GroupScheme.IsSplitTorus complexGroupScheme ∧
    ¬ GroupScheme.IsSplitTorus groupScheme

end Langlands.Shimura.DeligneTorus
