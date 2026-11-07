import Langlands.Global.NumberFieldProjectiveWeilAdeleEvaluation
import Langlands.Global.CurvePlaceProjectiveWeilAdeleEvaluation

/-! # The canonical adelic Weil comparison for quasi-projective schemes -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology

section NumberField

open NumberFieldProjectiveWeilAdeleHomeomorph

local instance numberFieldOriginalLocallyOfFiniteType
    (L : Type u) [Field L] (X : Scheme.{u}) (n : ℕ)
    (j : X ⟶ ProjectiveSpace L n) [IsImmersion j] :
    LocallyOfFiniteType (originalScheme L X n j).hom := by
  change LocallyOfFiniteType (j ≫ projectiveSpaceToSpec L n)
  infer_instance

/-- The canonical number-field counit is a homeomorphism for independent spread topologies. -/
def NumberFieldAdelicProjectiveWeilComparisonStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (X : Scheme.{u}) [CompactSpace X] (n : ℕ) (j : X ⟶ ProjectiveSpace L n)
    [IsImmersion j]
    (U : Finset (FinitePlace K)) (V : Finset (FinitePlace L))
    (P : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    (Q : Over (Spec (CommRingCat.of ((V : Set (FinitePlace L)).integer L))))
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (e : numberFieldModelGenericFiber K U P ≅
      affineChartWeilRestriction K L (originalScheme L X n j))
    (f : numberFieldModelGenericFiber L V Q ≅ originalScheme L X n j),
    @IsHomeomorph
      (NumberFieldAdelePoints K (affineChartWeilRestriction K L (originalScheme L X n j)))
      (NumberFieldAdelePoints L (originalScheme L X n j))
      (numberFieldSpreadAdelePointTopology K U P _ e)
      (numberFieldSpreadAdelePointTopology L V Q _ f)
      (NumberFieldProjectiveWeilAdeleEvaluation.adelicEvaluation K L X n j)

end NumberField

section Curve

open CurvePlaceProjectiveWeilAdeleHomeomorph

local instance curvePlaceOriginalLocallyOfFiniteType
    (L : Type u) [Field L] (X : Scheme.{u}) (n : ℕ)
    (j : X ⟶ ProjectiveSpace L n) [IsImmersion j] :
    LocallyOfFiniteType (originalScheme L X n j).hom := by
  change LocallyOfFiniteType (j ≫ projectiveSpaceToSpec L n)
  infer_instance

/-- The canonical function-field counit is a homeomorphism, including inseparable extensions. -/
def CurvePlaceAdelicProjectiveWeilComparisonStatement : Prop :=
  ∀ (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L],
    letI : Algebra (RatFunc k) L :=
      ((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra
    letI : IsScalarTower (RatFunc k) K L :=
      .of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower k (RatFunc k) L :=
      .of_algebraMap_eq fun a => by
        change algebraMap k L a =
          algebraMap K L (algebraMap (RatFunc k) K (algebraMap k (RatFunc k) a))
        rw [← IsScalarTower.algebraMap_apply k (RatFunc k) K,
          ← IsScalarTower.algebraMap_apply k K L]
    letI : FunctionField k L := Module.Finite.trans (R := RatFunc k) K L
    ∀ (X : Scheme.{u}) [CompactSpace X] (n : ℕ) (j : X ⟶ ProjectiveSpace L n)
      [IsImmersion j]
      (U : Finset (AlgebraicCurve.Place k K)) (V : Finset (AlgebraicCurve.Place k L))
      (P : Over (Spec (CommRingCat.of (curvePlaceSIntegers k K U))))
      (Q : Over (Spec (CommRingCat.of (curvePlaceSIntegers k L V))))
      [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
      [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
      (e : curvePlaceModelGenericFiber k K U P ≅
        affineChartWeilRestriction K L (originalScheme L X n j))
      (f : curvePlaceModelGenericFiber k L V Q ≅ originalScheme L X n j),
      @IsHomeomorph
        (CurvePlaceAdelePoints k K (affineChartWeilRestriction K L (originalScheme L X n j)))
        (CurvePlaceAdelePoints k L (originalScheme L X n j))
        (curvePlaceSpreadAdelePointTopology k K U P _ e)
        (curvePlaceSpreadAdelePointTopology k L V Q _ f)
        (CurvePlaceProjectiveWeilAdeleEvaluation.adelicEvaluation k K L X n j)

end Curve

/-- Conrad's Example 4.2 on actual adelic points in both characteristics, without model inputs. -/
def AdelicProjectiveWeilComparisonStatement : Prop :=
  CurvePlaceAdelicProjectiveWeilComparisonStatement.{u} ∧
    NumberFieldAdelicProjectiveWeilComparisonStatement.{u}

end Langlands.Global
