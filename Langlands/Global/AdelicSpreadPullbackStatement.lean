import Langlands.Global.AdelicGenericFiberPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemePullbackPoints
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Field-level adelic pullbacks for independent arithmetic spreads -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Any limiting field pullback over a separated base has its compatible-pair
topology for independently specified finite-type function-field spreads. -/
def CurvePlaceSpreadPullbackStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S T U : Finset (AlgebraicCurve.Place k F))
    (MX : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (MY : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F T))))
    (MP : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F U))))
    [LocallyOfFiniteType MX.hom] [QuasiCompact MX.hom]
    [LocallyOfFiniteType MY.hom] [QuasiCompact MY.hom]
    [LocallyOfFiniteType MP.hom] [QuasiCompact MP.hom]
    (X Y Z : Over (Spec (CommRingCat.of F))) [IsSeparated Z.hom]
    (eX : curvePlaceModelGenericFiber k F S MX ≅ X)
    (eY : curvePlaceModelGenericFiber k F T MY ≅ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g)
    (eP : curvePlaceModelGenericFiber k F U MP ≅ c.pt), IsLimit c →
    letI : TopologicalSpace (CurvePlaceAdelePoints k F X) :=
      curvePlaceSpreadAdelePointTopology k F S MX X eX
    letI : TopologicalSpace (CurvePlaceAdelePoints k F Y) :=
      curvePlaceSpreadAdelePointTopology k F T MY Y eY
    @IsHomeomorph (CurvePlaceAdelePoints k F c.pt)
      {q : CurvePlaceAdelePoints k F X × CurvePlaceAdelePoints k F Y //
        q.1 ≫ f = q.2 ≫ g}
      (curvePlaceSpreadAdelePointTopology k F U MP c.pt eP) inferInstance
      (affineSchemePullbackPointComparison F (CurvePlaceAdeleRing k F) c)

/-- The full-number-field comparison, including every infinite factor. -/
def NumberFieldSpreadPullbackStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S T U : Finset (FinitePlace K))
    (MX : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (MY : Over (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K))))
    (MP : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType MX.hom] [QuasiCompact MX.hom]
    [LocallyOfFiniteType MY.hom] [QuasiCompact MY.hom]
    [LocallyOfFiniteType MP.hom] [QuasiCompact MP.hom]
    (X Y Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom]
    (eX : numberFieldModelGenericFiber K S MX ≅ X)
    (eY : numberFieldModelGenericFiber K T MY ≅ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g)
    (eP : numberFieldModelGenericFiber K U MP ≅ c.pt), IsLimit c →
    letI : TopologicalSpace (NumberFieldAdelePoints K X) :=
      numberFieldSpreadAdelePointTopology K S MX X eX
    letI : TopologicalSpace (NumberFieldAdelePoints K Y) :=
      numberFieldSpreadAdelePointTopology K T MY Y eY
    @IsHomeomorph (NumberFieldAdelePoints K c.pt)
      {q : NumberFieldAdelePoints K X × NumberFieldAdelePoints K Y //
        q.1 ≫ f = q.2 ≫ g}
      (numberFieldSpreadAdelePointTopology K U MP c.pt eP) inferInstance
      (affineSchemePullbackPointComparison K (Adeles K) c)

/-- Both arithmetic forms of field-level pullback preservation over separated
bases with independent finite-type arithmetic spreads. -/
def AdelicSpreadPullbackStatement : Prop :=
  CurvePlaceSpreadPullbackStatement.{u} ∧ NumberFieldSpreadPullbackStatement.{u}

end Langlands.Global
