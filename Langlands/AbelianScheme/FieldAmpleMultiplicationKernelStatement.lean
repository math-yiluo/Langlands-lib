import Langlands.AbelianScheme.Multiplication
import Langlands.AbelianScheme.Kernel
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite multiplication kernel from an ample pullback identity -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An ample line bundle with the positive multiplication pullback identity
forces the whole scheme-theoretic multiplication kernel to be finite over the
ground field. This definition states the geometric target without proving it. -/
def FieldAmpleMultiplicationKernelStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left,
        L.IsAmple → ∀ n : ℕ, 0 < n →
          Nonempty
            ((_root_.AlgebraicGeometry.Scheme.Modules.pullback
              (multiplication G (n : ℤ)).hom.hom.left).obj L.obj ≅
                Langlands.Scheme.Modules.tensorPow L.obj (n * n)) →
          IsFinite (kernel (multiplication G (n : ℤ))).X.hom

end Langlands.GroupScheme
