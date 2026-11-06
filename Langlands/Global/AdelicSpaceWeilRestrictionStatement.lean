import Langlands.Global.AdelicSpacePointTopology
import Langlands.Global.AdelicTensorBaseChange
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestriction

/-!
# Adelic points of Weil restrictions of algebraic spaces

Conrad's Proposition 5.14: for a finite extension `F'/F` of global fields and a separated
algebraic space `X'` of finite type over `F'`, the Weil restriction `Res_{F'/F}(X')` is a
separated algebraic space of finite type over `F`, and the identification of its adelic
points with those of `X'` is a homeomorphism.
-/

universe u

open CategoryTheory
open scoped TensorProduct
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

/-- The function-field case of Conrad's Proposition 5.14. -/
def CurvePlaceSpaceWeilRestrictionStatement : Prop :=
  ∀ (k F F' : Type u) [Field k] [Finite k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
    [Algebra F F'] [IsScalarTower k F F'] [FiniteDimensional F F']
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [Algebra (RatFunc k) F'] [IsScalarTower k (RatFunc k) F'] [FunctionField k F']
    (Y' : AlgebraicSpace (Spec (CommRingCat.of F'))),
    IsSeparated Y' → FiniteTypeOverRing F' Y' →
    ∃ h : IsAlgebraicSpace _ ((ringWeilRestriction F F').obj Y'.toSheaf),
      IsSeparated (ringWeilRestrictionSpace F F' Y' h) ∧
      FiniteTypeOverRing F (ringWeilRestrictionSpace F F' Y' h) ∧
      ∀ (S : Finset (AlgebraicCurve.Place k F)) (S' : Finset (AlgebraicCurve.Place k F')),
        S.Nonempty → S'.Nonempty →
      ∀ (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
        (X' : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F' S')))),
        IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
        IsSeparated X' → FiniteTypeOverRing (curvePlaceSIntegers k F' S') X' →
      ∀ (e : curvePlaceSpaceGenericFiber k F S X ≅ ringWeilRestrictionSpace F F' Y' h)
        (e' : curvePlaceSpaceGenericFiber k F' S' X' ≅ Y'),
        @IsHomeomorph _ _
          (curvePlaceSpaceSpreadTopology k F S X (ringWeilRestrictionSpace F F' Y' h) e)
          (curvePlaceSpaceSpreadTopology k F' S' X' Y' e')
          (fun x => RingPoints.changeRing (curvePlaceAdeleTensorMap k F F')
            (ringWeilRestrictionPointsEquiv F F' (CurvePlaceAdeleRing k F) Y' h x))

/-- The number-field case of Conrad's Proposition 5.14. -/
def NumberFieldSpaceWeilRestrictionStatement : Prop :=
  ∀ (K K' : Type u) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (Y' : AlgebraicSpace (Spec (CommRingCat.of K'))),
    IsSeparated Y' → FiniteTypeOverRing K' Y' →
    ∃ h : IsAlgebraicSpace _ ((ringWeilRestriction K K').obj Y'.toSheaf),
      IsSeparated (ringWeilRestrictionSpace K K' Y' h) ∧
      FiniteTypeOverRing K (ringWeilRestrictionSpace K K' Y' h) ∧
      ∀ (S : Finset (FinitePlace K)) (S' : Finset (FinitePlace K'))
        (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
        (X' : AlgebraicSpace (Spec (CommRingCat.of ((S' : Set (FinitePlace K')).integer K')))),
        IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
        IsSeparated X' → FiniteTypeOverRing ((S' : Set (FinitePlace K')).integer K') X' →
      ∀ (e : numberFieldSpaceGenericFiber K S X ≅ ringWeilRestrictionSpace K K' Y' h)
        (e' : numberFieldSpaceGenericFiber K' S' X' ≅ Y'),
        @IsHomeomorph _ _
          (numberFieldSpaceSpreadTopology K S X (ringWeilRestrictionSpace K K' Y' h) e)
          (numberFieldSpaceSpreadTopology K' S' X' Y' e')
          (fun x => RingPoints.changeRing (numberFieldAdeleTensorMap K K')
            (ringWeilRestrictionPointsEquiv K K' (Adeles K) Y' h x))

/-- Conrad's Proposition 5.14 for global fields of both characteristics. -/
def AdelicSpaceWeilRestrictionStatement : Prop :=
  CurvePlaceSpaceWeilRestrictionStatement.{u} ∧ NumberFieldSpaceWeilRestrictionStatement.{u}

end Langlands.Global
