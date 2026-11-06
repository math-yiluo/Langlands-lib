import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Openness of adelic maps for smooth surjective maps with connected fibres

Conrad's Theorem 4.5: a smooth surjective map of separated schemes of finite type over a global
field, with geometrically connected fibres, induces an open map on adelic points.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Function fields: a smooth surjective map of separated schemes over `F` with geometrically
connected fibres induces an open map on adelic points, for arbitrary finite-type spreads. -/
def CurvePlaceSpreadSmoothOpenStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S U : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F U))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of F)))
    [_root_.AlgebraicGeometry.IsSeparated Y.hom] [_root_.AlgebraicGeometry.IsSeparated W.hom]
    (e : curvePlaceModelGenericFiber k F S X ≅ Y)
    (f : curvePlaceModelGenericFiber k F U Z ≅ W)
    (g : Y ⟶ W) [Smooth g.left] [Surjective g.left] [GeometricallyConnected g.left],
    @IsOpenMap (CurvePlaceAdelePoints k F Y) (CurvePlaceAdelePoints k F W)
      (curvePlaceSpreadAdelePointTopology k F S X Y e)
      (curvePlaceSpreadAdelePointTopology k F U Z W f)
      (fun p => p ≫ g)

/-- Number fields: a smooth surjective map of separated schemes over `K` with geometrically
connected fibres induces an open map on full-adele points, for arbitrary finite-type
spreads. -/
def NumberFieldSpreadSmoothOpenStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S U : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Z : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of K)))
    [_root_.AlgebraicGeometry.IsSeparated Y.hom] [_root_.AlgebraicGeometry.IsSeparated W.hom]
    (e : numberFieldModelGenericFiber K S X ≅ Y)
    (f : numberFieldModelGenericFiber K U Z ≅ W)
    (g : Y ⟶ W) [Smooth g.left] [Surjective g.left] [GeometricallyConnected g.left],
    @IsOpenMap (NumberFieldAdelePoints K Y) (NumberFieldAdelePoints K W)
      (numberFieldSpreadAdelePointTopology K S X Y e)
      (numberFieldSpreadAdelePointTopology K U Z W f)
      (fun p => p ≫ g)

/-- Conrad's Theorem 4.5 for global fields of both characteristics. -/
def AdelicSpreadSmoothOpenStatement : Prop :=
  CurvePlaceSpreadSmoothOpenStatement.{u} ∧ NumberFieldSpreadSmoothOpenStatement.{u}

end Langlands.Global
