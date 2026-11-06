import Langlands.Global.AdelicGenericFiberPoints

/-!
# Agreement of the adelic spread topology with the affine topology

Conrad, Section 4, printed p.9: the topology on `X(A_F)` coincides with the topology of
Proposition 2.1 when `X` is affine.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Function fields: for an affine scheme over `F` with a finite-type spread, the topology on
its full-adele points attached to the spread is the affine point topology. -/
def CurvePlaceSpreadAffineTopologyStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of F))) [IsAffine Y.left]
    (e : curvePlaceModelGenericFiber k F S X ≅ Y),
    curvePlaceSpreadAdelePointTopology k F S X Y e =
      (inferInstance : TopologicalSpace (CurvePlaceAdelePoints k F Y))

/-- Number fields: for an affine scheme over `K` with a finite-type spread, the topology on
its full-adele points attached to the spread is the affine point topology. -/
def NumberFieldSpreadAffineTopologyStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of K))) [IsAffine Y.left]
    (e : numberFieldModelGenericFiber K S X ≅ Y),
    numberFieldSpreadAdelePointTopology K S X Y e =
      (inferInstance : TopologicalSpace (NumberFieldAdelePoints K Y))

/-- Conrad's p.9 agreement of the adelic topology with the affine topology, for global fields
of both characteristics. -/
def AdelicSpreadAffineTopologyStatement : Prop :=
  CurvePlaceSpreadAffineTopologyStatement.{u} ∧ NumberFieldSpreadAffineTopologyStatement.{u}

end Langlands.Global
