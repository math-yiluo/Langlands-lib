import Langlands.AbelianScheme.Multiplication
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Existence of symmetric ample line bundles over a field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every commutative smooth proper geometrically connected group scheme over
any field admits an ample line bundle isomorphic to its inverse pullback.
This proposition is a statement target, not a proof. -/
def FieldSymmetricAmpleExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∃ L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left,
        L.IsAmple ∧ Nonempty
          ((_root_.AlgebraicGeometry.Scheme.Modules.pullback
            (multiplication G (-1)).hom.hom.left).obj L.obj ≅ L.obj)

end Langlands.GroupScheme
