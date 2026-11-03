import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionMaps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Closed-immersion preservation by actual finite-type affine Weil restriction -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

open Langlands.Algebra

/-- The algebraic and actual-scheme forms of closed-immersion preservation
in Conrad Example 2.4. Each input algebra or affine scheme is finite type. -/
def WeilRestrictionClosedImmersionProperties
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Projective A B] : Prop :=
  (∀ (C D : Type u) [CommRing C] [CommRing D] [Algebra B C] [Algebra B D]
      [Algebra.FiniteType B C] [Algebra.FiniteType B D] (φ : C →ₐ[B] D),
    Function.Surjective φ → Function.Surjective (WeilRestrictionFiniteType.map A B φ)) ∧
  (∀ (X Y : Over (Spec (CommRingCat.of B)))
      [IsAffine X.left] [IsAffine Y.left]
      [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y),
    IsClosedImmersion f.left → IsClosedImmersion (affineWeilRestrictionMap A B f).left)

end Langlands.AlgebraicGeometry.PointTopology
