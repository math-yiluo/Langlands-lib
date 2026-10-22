import Langlands.AbelianScheme.Multiplication
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Multiplication pullback of symmetric line bundles over a field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- On a commutative smooth proper geometrically connected group scheme over
any field, pulling a symmetric line bundle back by positive multiplication by
`n` gives its actual `n * n`-th tensor power. This is a statement target. -/
def FieldSymmetricMultiplicationPullbackStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∀ (L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left),
        Nonempty
          ((_root_.AlgebraicGeometry.Scheme.Modules.pullback
            (multiplication G (-1)).hom.hom.left).obj L.obj ≅ L.obj) →
        ∀ (n : ℕ), 0 < n →
          Nonempty
            ((_root_.AlgebraicGeometry.Scheme.Modules.pullback
              (multiplication G (n : ℤ)).hom.hom.left).obj L.obj ≅
                Langlands.Scheme.Modules.tensorPow L.obj (n * n))

end Langlands.GroupScheme
