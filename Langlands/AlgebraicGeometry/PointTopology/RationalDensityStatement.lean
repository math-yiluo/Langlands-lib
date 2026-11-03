import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Elementary Zariski density toolkit for actual rational points -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The union of the images of actual rational points is Zariski dense. -/
def HasDenseRationalPoints (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) : Prop :=
  Dense (⋃ p : RationalPoint k X, Set.range p.left)

/-- Affine spaces over infinite fields have dense rational points; this
property restricts to open subschemes and descends along dominant morphisms. -/
def RationalPointDensityToolkitStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k],
    (∀ (n : Type u), HasDenseRationalPoints k
      (Over.mk (𝔸(n; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))) ∧
    (∀ (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens),
      HasDenseRationalPoints k X →
      HasDenseRationalPoints k (Over.mk (U.ι ≫ X.hom))) ∧
    (∀ (X Y : Over (Spec (CommRingCat.of k))) (f : X ⟶ Y),
      DenseRange f.left → HasDenseRationalPoints k X →
      HasDenseRationalPoints k Y)

end Langlands.AlgebraicGeometry.PointTopology
