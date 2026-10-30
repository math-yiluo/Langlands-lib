import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The theorem of the square for line bundles on abelian group schemes over a field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For every line bundle `L` on a commutative smooth proper geometrically connected group
scheme over a field `K` and all rational points `a, b`, writing `Q c` for the pullback of
`L` along translation by `c`, the module sheaves `Q (a * b) ⊗ L` and `Q a ⊗ Q b` are
isomorphic. This proposition is a statement target, not a proof. -/
def FieldTheoremOfTheSquareStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∀ (L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left)
        (a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X),
        Nonempty (Langlands.Scheme.Modules.tensorObj
            ((_root_.AlgebraicGeometry.Scheme.Modules.pullback
              (translation G (a * b)).left).obj L.obj) L.obj ≅
          Langlands.Scheme.Modules.tensorObj
            ((_root_.AlgebraicGeometry.Scheme.Modules.pullback
              (translation G a).left).obj L.obj)
            ((_root_.AlgebraicGeometry.Scheme.Modules.pullback
              (translation G b).left).obj L.obj))

end Langlands.GroupScheme
