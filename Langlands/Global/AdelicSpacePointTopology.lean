import Langlands.Global.AdelicSpaceLevelTopology
import Langlands.Global.AdelicFixedModelCocone
import Langlands.Global.CurvePlaceAdeleDiagonal

/-!
# Topology on adelic points of algebraic spaces

For an algebraic space `X` over the `S`-integers of a global field, the points of `X` with
values in a level `A_{F,T}`, `T ⊇ S`, carry the level topology of the base change of `X` to
the `T`-integers. The full adelic points `X(A_F)` carry the final topology from these stages,
as in Conrad's Section 4 and printed p.17. A specified isomorphism from the generic fibre of
`X` to an algebraic space `Y` over the global field transports this topology to `Y(A_F)`.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {C : Type u} [CommRing C] {A : Type u} [CommRing A] [Algebra C A]

/-- An isomorphism of algebraic spaces identifies their `A`-valued points. -/
def RingPoints.mapEquiv {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (e : X ≅ Y) :
    RingPoints C X A ≃ RingPoints C Y A where
  toFun := RingPoints.map e.hom
  invFun := RingPoints.map e.inv
  left_inv x := by rw [← RingPoints.map_comp, e.hom_inv_id, RingPoints.map_id]
  right_inv x := by rw [← RingPoints.map_comp, e.inv_hom_id, RingPoints.map_id]

end Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- The points of `X` over the `T`-level, viewed over the `S`-integers, are the points of the
base change of `X` to the `T`-integers. -/
def curvePlaceSpaceStageEquiv (T : AdelicLevelIndexAbove S) :
    RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) ≃
      RingPoints (curvePlaceSIntegers k F T.val)
        (curvePlaceSpaceLevelBaseChange k F T.property X) (curvePlaceAdeleLevel k F T.val) := by
  letI : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  letI : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  letI : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (baseChangeRingPointsEquiv (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
    (curvePlaceAdeleLevelOver k F S T) X).symm

/-- The stage topology: the level topology of the base change, transported along the stage
equivalence. -/
@[instance_reducible]
def curvePlaceSpaceStageTopology (T : AdelicLevelIndexAbove S) :
    TopologicalSpace
      (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :=
  TopologicalSpace.induced (curvePlaceSpaceStageEquiv k F S X T)
    (curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X))

/-- The full adelic points of `X`, with the full adele ring as an algebra over the
`S`-integers. -/
abbrev CurvePlaceSpaceAdelePoints :=
  RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleOver k F S)

/-- The map from the points over the `T`-level to the full adelic points. -/
def curvePlaceSpaceStageMap (T : AdelicLevelIndexAbove S) :
    RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) →
      CurvePlaceSpaceAdelePoints k F S X :=
  RingPoints.changeRing (curvePlaceAdeleLevelOverι k F S T).hom

/-- The topology on the full adelic points: final for the stage maps. -/
@[instance_reducible]
def curvePlaceSpaceAdelePointTopology :
    TopologicalSpace (CurvePlaceSpaceAdelePoints k F S X) :=
  ⨆ T : AdelicLevelIndexAbove S,
    @TopologicalSpace.coinduced _ _ (curvePlaceSpaceStageMap k F S X T)
      (curvePlaceSpaceStageTopology k F S X T)

/-- The generic fibre of `X`: its base change to the function field. -/
def curvePlaceSpaceGenericFiber : AlgebraicSpace (Spec (CommRingCat.of F)) :=
  baseChange (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) X

variable [PerfectField k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FunctionField k F]

/-- The full adelic points of an algebraic space over the function field. -/
abbrev CurvePlaceSpaceFieldAdelePoints (Y : AlgebraicSpace (Spec (CommRingCat.of F))) :=
  RingPoints F Y (CurvePlaceAdeleRing k F)

/-- The adelic points of `X` are the adelic points of its generic fibre. -/
def curvePlaceSpaceGenericFiberEquiv :
    CurvePlaceSpaceAdelePoints k F S X ≃
      CurvePlaceSpaceFieldAdelePoints k F (curvePlaceSpaceGenericFiber k F S X) := by
  let algSF : Algebra (curvePlaceSIntegers k F S) F :=
    (curvePlaceSIntegers k F S).subtype.toAlgebra
  let algSA : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S) :=
    (curvePlaceAdeleOver k F S).algebra
  let algFA : Algebra F (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra F (CurvePlaceAdeleRing k F))
  let tower := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSF algFA algSA
    (curvePlaceAdeleLevelDiagonal_eq k F S)
  exact (@baseChangeRingPointsEquiv (curvePlaceSIntegers k F S) F _ _ algSF
    (curvePlaceAdeleOver k F S) _ algSA algFA tower X).symm

variable (Y : AlgebraicSpace (Spec (CommRingCat.of F)))
variable (e : curvePlaceSpaceGenericFiber k F S X ≅ Y)

/-- A specified isomorphism from the generic fibre identifies the adelic points of `X` with
those of `Y`. -/
def curvePlaceSpaceSpreadEquiv :
    CurvePlaceSpaceAdelePoints k F S X ≃ CurvePlaceSpaceFieldAdelePoints k F Y :=
  (curvePlaceSpaceGenericFiberEquiv k F S X).trans (RingPoints.mapEquiv e)

/-- The topology on the adelic points of `Y` attached to the spread `(S, X, e)`. -/
@[instance_reducible]
def curvePlaceSpaceSpreadTopology : TopologicalSpace (CurvePlaceSpaceFieldAdelePoints k F Y) :=
  TopologicalSpace.induced (curvePlaceSpaceSpreadEquiv k F S X Y e).symm
    (curvePlaceSpaceAdelePointTopology k F S X)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
variable (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

/-- The points of `X` over the `T`-level, viewed over the `S`-integers, are the points of the
base change of `X` to the `T`-integers. -/
def numberFieldSpaceStageEquiv (T : AdelicLevelIndexAbove S) :
    RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T) ≃
      RingPoints ((T.val : Set (FinitePlace K)).integer K)
        (numberFieldSpaceLevelBaseChange K T.property X) (numberFieldAdeleLevel K T.val) := by
  letI : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  letI : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  letI : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) X).symm

/-- The stage topology: the level topology of the base change, transported along the stage
equivalence. -/
@[instance_reducible]
def numberFieldSpaceStageTopology (T : AdelicLevelIndexAbove S) :
    TopologicalSpace
      (RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :=
  TopologicalSpace.induced (numberFieldSpaceStageEquiv K S X T)
    (numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X))

/-- The full adelic points of `X`, with the full adele ring as an algebra over the
`S`-integers. -/
abbrev NumberFieldSpaceAdelePoints :=
  RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleOver K S)

/-- The map from the points over the `T`-level to the full adelic points. -/
def numberFieldSpaceStageMap (T : AdelicLevelIndexAbove S) :
    RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T) →
      NumberFieldSpaceAdelePoints K S X :=
  RingPoints.changeRing (numberFieldAdeleLevelOverι K S T).hom

/-- The topology on the full adelic points: final for the stage maps. -/
@[instance_reducible]
def numberFieldSpaceAdelePointTopology :
    TopologicalSpace (NumberFieldSpaceAdelePoints K S X) :=
  ⨆ T : AdelicLevelIndexAbove S,
    @TopologicalSpace.coinduced _ _ (numberFieldSpaceStageMap K S X T)
      (numberFieldSpaceStageTopology K S X T)

/-- The generic fibre of `X`: its base change to the number field. -/
def numberFieldSpaceGenericFiber : AlgebraicSpace (Spec (CommRingCat.of K)) :=
  baseChange
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) X

/-- The full adelic points of an algebraic space over the number field. -/
abbrev NumberFieldSpaceFieldAdelePoints (Y : AlgebraicSpace (Spec (CommRingCat.of K))) :=
  RingPoints K Y (Adeles K)

/-- The adelic points of `X` are the adelic points of its generic fibre. -/
def numberFieldSpaceGenericFiberEquiv :
    NumberFieldSpaceAdelePoints K S X ≃
      NumberFieldSpaceFieldAdelePoints K (numberFieldSpaceGenericFiber K S X) := by
  let algSK : Algebra ((S : Set (FinitePlace K)).integer K) K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let algSA : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K S).algebra
  let algKA : Algebra K (numberFieldAdeleOver K S) := inferInstanceAs (Algebra K (Adeles K))
  let tower := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSK algKA algSA (fun _ => rfl)
  exact (@baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K) K _ _ algSK
    (numberFieldAdeleOver K S) _ algSA algKA tower X).symm

variable (Y : AlgebraicSpace (Spec (CommRingCat.of K)))
variable (e : numberFieldSpaceGenericFiber K S X ≅ Y)

/-- A specified isomorphism from the generic fibre identifies the adelic points of `X` with
those of `Y`. -/
def numberFieldSpaceSpreadEquiv :
    NumberFieldSpaceAdelePoints K S X ≃ NumberFieldSpaceFieldAdelePoints K Y :=
  (numberFieldSpaceGenericFiberEquiv K S X).trans (RingPoints.mapEquiv e)

/-- The topology on the adelic points of `Y` attached to the spread `(S, X, e)`. -/
@[instance_reducible]
def numberFieldSpaceSpreadTopology : TopologicalSpace (NumberFieldSpaceFieldAdelePoints K Y) :=
  TopologicalSpace.induced (numberFieldSpaceSpreadEquiv K S X Y e).symm
    (numberFieldSpaceAdelePointTopology K S X)

end NumberField

end Langlands.Global
