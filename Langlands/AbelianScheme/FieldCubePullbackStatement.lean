import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The balanced cube pullback identity over a field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The balanced cube identity for actual line-bundle pullbacks along three
maps from an arbitrary scheme over a field to an abelian variety.
This definition records a statement target, not its proof. -/
def FieldCubePullbackStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∀ (T : Over (Spec (CommRingCat.of K))) (f g h : T ⟶ G.X)
        (L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left),
        let Q := fun (a : T ⟶ G.X) =>
          (_root_.AlgebraicGeometry.Scheme.Modules.pullback a.left).obj L.obj
        Nonempty
          (Langlands.Scheme.Modules.tensorObj (Q (f * g * h))
            (Langlands.Scheme.Modules.tensorObj (Q f)
              (Langlands.Scheme.Modules.tensorObj (Q g) (Q h))) ≅
           Langlands.Scheme.Modules.tensorObj (Q (f * g))
            (Langlands.Scheme.Modules.tensorObj (Q (f * h)) (Q (g * h))))

end Langlands.GroupScheme
