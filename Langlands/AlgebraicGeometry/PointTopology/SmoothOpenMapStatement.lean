import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Openness of smooth maps on rational points over local fields

The proposition below asserts that a smooth morphism of affine schemes over a nonarchimedean
local field induces an open map between the canonical evaluation topologies on rational points.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- For every nonarchimedean local field `F` and every smooth morphism `f : X ⟶ Y` of affine
schemes over `Spec F`, postcomposition with `f` is an open map from the rational points of `X`
to those of `Y`, both carrying `rationalPointTopology`. -/
def SmoothRationalPointOpenMapStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (X Y : Over (Spec (CommRingCat.of F))) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [Smooth f.left],
    letI : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
    letI : TopologicalSpace (RationalPoint F Y) := rationalPointTopology F Y
    IsOpenMap (fun p : RationalPoint F X => p ≫ f)

end Langlands.AlgebraicGeometry.PointTopology
