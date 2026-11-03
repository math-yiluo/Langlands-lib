import Langlands.AbelianScheme.GroupScheme
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Rational points of torsors over finite fields -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- An actual fpqc torsor under a smooth connected affine group over a finite
field has a rational point. The action and its shear are actual scheme maps. -/
def FiniteFieldTorsorPointStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom],
    ConnectedSpace H.X.left →
    ∀ (X : Over (Spec (CommRingCat.of k))) [ModObj H.X X],
      Flat X.hom → Surjective X.hom → QuasiCompact X.hom →
      IsIso (ModObj.leftSMul H.X X) → Nonempty (RingPoint k X k)

end Langlands.GroupScheme
