import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPointsEquivalence
import Langlands.Global.AdelicSpaceWeilRestrictionStatement
import Langlands.Global.CurvePlaceAdeleTensorComparison
import Langlands.Global.NumberFieldAdeleTensorComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsGluing

/-!
# The canonical bijection on adelic points of a Weil restriction

The published tensor comparisons give the bijection in Conrad's Proposition 5.14,
before any assertion about topology or the existence of the Weil restriction as
an algebraic space. Representability is an explicit input to these constructions.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace


variable (R R' A B : Type u) [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
variable [Algebra R R'] [Algebra R A] [Algebra R' B]
variable (X' : AlgebraicSpace (Spec (CommRingCat.of R')))
variable (h : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj X'.toSheaf))

/-- The Weil point equivalence followed by a specified tensor-algebra equivalence. -/
def ringWeilRestrictionPointsEquivOfAlgEquiv (e : R' ⊗[R] A ≃ₐ[R'] B) :
    RingPoints R (ringWeilRestrictionSpace R R' X' h) A ≃ RingPoints R' X' B :=
  (ringWeilRestrictionPointsEquiv R R' A X' h).trans (RingPoints.changeRingEquiv X' e)

@[simp]
theorem ringWeilRestrictionPointsEquivOfAlgEquiv_apply (e : R' ⊗[R] A ≃ₐ[R'] B)
    (x : RingPoints R (ringWeilRestrictionSpace R R' X' h) A) :
    ringWeilRestrictionPointsEquivOfAlgEquiv R R' A B X' h e x =
      RingPoints.changeRing e.toAlgHom (ringWeilRestrictionPointsEquiv R R' A X' h x) :=
  rfl

variable {R R' A B X'}

/-- The tensor comparison is natural in the original algebraic space. -/
theorem ringWeilRestrictionPointsEquivOfAlgEquiv_map
    {Y' : AlgebraicSpace (Spec (CommRingCat.of R'))}
    (hY : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj Y'.toSheaf))
    (f : X' ⟶ Y') (e : R' ⊗[R] A ≃ₐ[R'] B)
    (x : RingPoints R (ringWeilRestrictionSpace R R' X' h) A) :
    ringWeilRestrictionPointsEquivOfAlgEquiv R R' A B Y' hY e
        (RingPoints.map (ringWeilRestrictionSpaceMap R R' h hY f) x) =
      RingPoints.map f (ringWeilRestrictionPointsEquivOfAlgEquiv R R' A B X' h e x) := by
  simp only [ringWeilRestrictionPointsEquivOfAlgEquiv_apply,
    ringWeilRestrictionPointsEquiv_map, RingPoints.changeRing_map]

end Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

section Curve

variable (k F F' : Type u) [Field k] [Finite k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable [FiniteDimensional F F']
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable [Algebra (RatFunc k) F'] [IsScalarTower k (RatFunc k) F'] [FunctionField k F']
variable (Y' : AlgebraicSpace (Spec (CommRingCat.of F')))
variable (h : IsAlgebraicSpace _ ((ringWeilRestriction F F').obj Y'.toSheaf))

/-- The canonical curve-place adelic point bijection, including inseparable extensions. -/
def curvePlaceSpaceWeilRestrictionPointsEquiv :
    RingPoints F (ringWeilRestrictionSpace F F' Y' h) (CurvePlaceAdeleRing k F) ≃
      RingPoints F' Y' (CurvePlaceAdeleRing k F') :=
  ringWeilRestrictionPointsEquivOfAlgEquiv F F' _ _ Y' h
    (curvePlaceAdeleTensorEquiv k F F')

/-- Its forward map is exactly the map in the published adelic statement. -/
@[simp]
theorem curvePlaceSpaceWeilRestrictionPointsEquiv_apply
    (x : RingPoints F (ringWeilRestrictionSpace F F' Y' h) (CurvePlaceAdeleRing k F)) :
    curvePlaceSpaceWeilRestrictionPointsEquiv k F F' Y' h x =
      RingPoints.changeRing (curvePlaceAdeleTensorMap k F F')
        (ringWeilRestrictionPointsEquiv F F' (CurvePlaceAdeleRing k F) Y' h x) := rfl

end Curve

section NumberField

variable (K K' : Type u) [Field K] [NumberField K] [Field K'] [NumberField K']
variable [Algebra K K']
variable (Y' : AlgebraicSpace (Spec (CommRingCat.of K')))
variable (h : IsAlgebraicSpace _ ((ringWeilRestriction K K').obj Y'.toSheaf))

/-- The canonical full number-field adelic point bijection. -/
def numberFieldSpaceWeilRestrictionPointsEquiv :
    RingPoints K (ringWeilRestrictionSpace K K' Y' h) (Adeles K) ≃
      RingPoints K' Y' (Adeles K') :=
  ringWeilRestrictionPointsEquivOfAlgEquiv K K' _ _ Y' h
    (numberFieldAdeleTensorEquiv K K')

/-- Its forward map is exactly the map in the published adelic statement. -/
@[simp]
theorem numberFieldSpaceWeilRestrictionPointsEquiv_apply
    (x : RingPoints K (ringWeilRestrictionSpace K K' Y' h) (Adeles K)) :
    numberFieldSpaceWeilRestrictionPointsEquiv K K' Y' h x =
      RingPoints.changeRing (numberFieldAdeleTensorMap K K')
        (ringWeilRestrictionPointsEquiv K K' (Adeles K) Y' h x) := rfl

end NumberField

end Langlands.Global
