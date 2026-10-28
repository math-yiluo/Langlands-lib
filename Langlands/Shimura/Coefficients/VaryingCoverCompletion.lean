import Langlands.Shimura.Coefficients.DiagramCompletion
import Langlands.Shimura.Coefficients.VaryingCoverPowerLimits

/-! # Associated completed coefficients and the limit of associated quotients -/

noncomputable section

universe u uJ vJ

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {J : Type uJ} [Category.{vJ} J] {D : J ⥤ GrpCat.{u}}
variable (X : Scheme.{u}) (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j))

/-- Form associated sheaf diagrams after actual module completion. -/
def etaleAssociatedCompletedCoefficientFunctor :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  coefficientDiagramCompletion I ⋙ etaleAssociatedVaryingSystemFunctor X Y hY

/-- Apply the actual associated-diagram functor to the completion evaluation cone. -/
def etaleAssociatedCompletionCone (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    Cone ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M) :=
  (etaleAssociatedVaryingSystemFunctor X Y hY).mapCone
    (coefficientDiagramCompletionCone I M)

@[simp] theorem etaleAssociatedCompletionCone_π
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    (etaleAssociatedCompletionCone I X Y hY M).π.app (op n) =
      (etaleAssociatedVaryingSystemFunctor X Y hY).map
        ((coefficientDiagramCompletionProjection I n).app M) := rfl

/-- The canonical map from associated completed coefficients to associated quotient limits. -/
def etaleAssociatedCompletionComparison :
    etaleAssociatedCompletedCoefficientFunctor I X Y hY ⟶
      etaleAssociatedCoefficientPowerLimit I X Y hY where
  app M := limit.lift _ (etaleAssociatedCompletionCone I X Y hY M)
  naturality {M N} c := by
    change (etaleAssociatedVaryingSystemFunctor X Y hY).map
        ((coefficientDiagramCompletion I).map c) ≫
          limit.lift _ (etaleAssociatedCompletionCone I X Y hY N) =
      limit.lift _ (etaleAssociatedCompletionCone I X Y hY M) ≫
        limMap ((etaleAssociatedCoefficientPowerSystems I X Y hY).map c)
    apply limit.hom_ext
    intro n
    rw [Category.assoc, limit.lift_π, Category.assoc, limMap_π,
      ← Category.assoc, limit.lift_π]
    change (etaleAssociatedVaryingSystemFunctor X Y hY).map
        ((coefficientDiagramCompletion I).map c) ≫
          (etaleAssociatedVaryingSystemFunctor X Y hY).map
            ((coefficientDiagramCompletionProjection I n.unop).app N) =
      (etaleAssociatedVaryingSystemFunctor X Y hY).map
          ((coefficientDiagramCompletionProjection I n.unop).app M) ≫
        (etaleAssociatedVaryingSystemFunctor X Y hY).map
          (((coefficientDiagramPowers I).obj n).map c)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (fun a => (etaleAssociatedVaryingSystemFunctor X Y hY).map a)
      ((coefficientDiagramCompletionProjection I n.unop).naturality c)

/-- Each projection is exactly the associated map of the genuine completion evaluation. -/
@[reassoc (attr := simp)]
theorem etaleAssociatedCompletionComparison_π
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    (etaleAssociatedCompletionComparison I X Y hY).app M ≫
        limit.π ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M) (op n) =
      (etaleAssociatedVaryingSystemFunctor X Y hY).map
        ((coefficientDiagramCompletionProjection I n).app M) :=
  limit.lift_π _ _

/-- The original associated-diagram unit factors through associated completed coefficients. -/
theorem etaleAssociatedCompletionComparison_unit :
    Functor.whiskerRight (coefficientDiagramCompletionUnit I)
        (etaleAssociatedVaryingSystemFunctor X Y hY) ≫
      etaleAssociatedCompletionComparison I X Y hY =
        etaleAssociatedCoefficientPowerLimitUnit I X Y hY := by
  apply NatTrans.ext
  funext M
  apply limit.hom_ext
  intro n
  change ((etaleAssociatedVaryingSystemFunctor X Y hY).map
      ((coefficientDiagramCompletionUnit I).app M) ≫
        (etaleAssociatedCompletionComparison I X Y hY).app M) ≫
          limit.π ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M) n =
    (etaleAssociatedCoefficientPowerLimitUnit I X Y hY).app M ≫
      limit.π ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M) n
  rw [Category.assoc, etaleAssociatedCompletionComparison_π,
    etaleAssociatedCoefficientPowerLimitUnit_π, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun a => (etaleAssociatedVaryingSystemFunctor X Y hY).map a)
    (congrArg (fun a => a.app M)
      (coefficientDiagramCompletionUnit_projection (D := D) I n.unop))

/-- The actual quotient projections characterize the comparison uniquely. -/
theorem etaleAssociatedCompletionComparison_unique
    (M : EquivariantDiagram D (ModuleCat.{u} R))
    (f : (etaleAssociatedCompletedCoefficientFunctor I X Y hY).obj M ⟶
      (etaleAssociatedCoefficientPowerLimit I X Y hY).obj M)
    (hf : ∀ n : ℕ,
      f ≫ limit.π ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M) (op n) =
        (etaleAssociatedVaryingSystemFunctor X Y hY).map
          ((coefficientDiagramCompletionProjection I n).app M)) :
    f = (etaleAssociatedCompletionComparison I X Y hY).app M := by
  apply limit.hom_ext
  intro n
  exact (hf n.unop).trans (etaleAssociatedCompletionComparison_π I X Y hY M n.unop).symm

/-- Under cover evaluation, every limit projection is the corresponding associated evaluation. -/
@[reassoc (attr := simp)]
theorem etaleAssociatedCompletionComparison_evaluation_π
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (j : J) (n : ℕ) :
    ((etaleAssociatedCompletionComparison I X Y hY).app M).app j ≫
        (etaleAssociatedCoefficientPowerLimitEvaluationIso I X Y hY M j).hom ≫
          limit.π _ (op n) =
      ((etaleAssociatedVaryingSystemFunctor X Y hY).map
        ((coefficientDiagramCompletionProjection I n).app M)).app j := by
  rw [etaleAssociatedCoefficientPowerLimitEvaluationIso_hom_π]
  exact congrArg (fun a => a.app j) (etaleAssociatedCompletionComparison_π I X Y hY M n)

end Langlands.Shimura.Coefficients
