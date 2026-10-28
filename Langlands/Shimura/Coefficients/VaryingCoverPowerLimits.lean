import Langlands.Shimura.Coefficients.VaryingCoverPowerSystems
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Ordinary coefficient-power limits of associated sheaf diagrams -/

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

/-- Take the ordinary inverse limit of the associated coefficient-power diagrams. -/
def etaleAssociatedCoefficientPowerLimit :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  etaleAssociatedCoefficientPowerSystems I X Y hY ⋙ lim

/-- Take the ordinary inverse limit of the sheaf-power diagrams. -/
def etaleAssociatedSheafPowerLimit :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  etaleAssociatedSheafPowerSystems I X Y hY ⋙ lim

/-- The canonical reduction comparison induces a morphism between these actual limits. -/
def etaleAssociatedPowerLimitComparison :
    etaleAssociatedSheafPowerLimit I X Y hY ⟶
      etaleAssociatedCoefficientPowerLimit I X Y hY :=
  Functor.whiskerRight (etaleAssociatedVaryingReductionSystemsComparison I X Y hY) lim

/-- The genuine sheaf quotient units form a cone on the complete cover diagram. -/
def etaleAssociatedSheafPowerCone (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    Cone ((etaleAssociatedSheafPowerSystems I X Y hY).obj M) where
  pt := (etaleAssociatedVaryingSystemFunctor X Y hY).obj M
  π :=
    { app n := Functor.whiskerLeft (etaleAssociatedVaryingSystem X Y hY M)
        (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n.unop)
      naturality {_m _n} f := by
        apply NatTrans.ext
        funext j
        change
          (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I _n.unop).app
              ((etaleAssociatedVaryingSystem X Y hY M).obj j) =
            (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I _m.unop).app
                ((etaleAssociatedVaryingSystem X Y hY M).obj j) ≫
              ((Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I).map f).app
                ((etaleAssociatedVaryingSystem X Y hY M).obj j)
        simpa only [NatTrans.comp_app,
          show (homOfLE (leOfHom f.unop)).op = f from Subsingleton.elim _ _] using
          (congrArg (fun a => a.app ((etaleAssociatedVaryingSystem X Y hY M).obj j))
            (Langlands.Sheaf.AdicSystem.quotientMap_transition X.smallEtaleTopology I
              (leOfHom f.unop))).symm }

/-- Postcompose the quotient cone with the actual coefficient comparison. -/
def etaleAssociatedCoefficientPowerCone (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    Cone ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M) :=
  (Cone.postcompose ((etaleAssociatedVaryingReductionSystemsComparison I X Y hY).app M)).obj
    (etaleAssociatedSheafPowerCone I X Y hY M)

/-- Its leg is exactly the image of the actual coefficient-diagram quotient map. -/
@[simp] theorem etaleAssociatedCoefficientPowerCone_π
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    (etaleAssociatedCoefficientPowerCone I X Y hY M).π.app (op n) =
      (etaleAssociatedVaryingSystemFunctor X Y hY).map
        ((coefficientDiagramPowerUnit I n).app M) :=
  etaleAssociatedVaryingReductionSystemsComparison_unit I X Y hY M n

/-- The canonical map from the original associated diagram to its sheaf-power limit. -/
def etaleAssociatedSheafPowerLimitUnit :
    etaleAssociatedVaryingSystemFunctor X Y hY ⟶
      etaleAssociatedSheafPowerLimit I X Y hY where
  app M := limit.lift _ (etaleAssociatedSheafPowerCone I X Y hY M)
  naturality {M N} c := by
    change (etaleAssociatedVaryingSystemFunctor X Y hY).map c ≫
        limit.lift _ (etaleAssociatedSheafPowerCone I X Y hY N) =
      limit.lift _ (etaleAssociatedSheafPowerCone I X Y hY M) ≫
        limMap ((etaleAssociatedSheafPowerSystems I X Y hY).map c)
    apply limit.hom_ext
    intro n
    rw [Category.assoc, limit.lift_π, Category.assoc, limMap_π,
      ← Category.assoc, limit.lift_π]
    apply NatTrans.ext
    funext j
    exact (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n.unop).naturality
      (((etaleAssociatedVaryingSystemFunctor X Y hY).map c).app j)

/-- The canonical map into the limit of the associated coefficient quotients. -/
def etaleAssociatedCoefficientPowerLimitUnit :
    etaleAssociatedVaryingSystemFunctor X Y hY ⟶
      etaleAssociatedCoefficientPowerLimit I X Y hY :=
  etaleAssociatedSheafPowerLimitUnit I X Y hY ≫
    etaleAssociatedPowerLimitComparison I X Y hY

@[reassoc (attr := simp)]
theorem etaleAssociatedSheafPowerLimitUnit_π
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    (etaleAssociatedSheafPowerLimitUnit I X Y hY).app M ≫
        limit.π ((etaleAssociatedSheafPowerSystems I X Y hY).obj M) (op n) =
      Functor.whiskerLeft (etaleAssociatedVaryingSystem X Y hY M)
        (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n) :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
theorem etaleAssociatedPowerLimitComparison_π
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    (etaleAssociatedPowerLimitComparison I X Y hY).app M ≫
        limit.π ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M) (op n) =
      limit.π ((etaleAssociatedSheafPowerSystems I X Y hY).obj M) (op n) ≫
        ((etaleAssociatedVaryingReductionSystemsComparison I X Y hY).app M).app (op n) :=
  limMap_π _ _

@[reassoc (attr := simp)]
theorem etaleAssociatedCoefficientPowerLimitUnit_π
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    (etaleAssociatedCoefficientPowerLimitUnit I X Y hY).app M ≫
        limit.π ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M) (op n) =
      (etaleAssociatedVaryingSystemFunctor X Y hY).map
        ((coefficientDiagramPowerUnit I n).app M) := by
  simp only [etaleAssociatedCoefficientPowerLimitUnit, NatTrans.comp_app, Category.assoc,
    etaleAssociatedPowerLimitComparison_π, etaleAssociatedSheafPowerLimitUnit_π_assoc]
  exact etaleAssociatedVaryingReductionSystemsComparison_unit I X Y hY M n

/-- The coefficient-limit unit is the universal map from the genuine coefficient cone. -/
theorem etaleAssociatedCoefficientPowerLimitUnit_eq_lift
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedCoefficientPowerLimitUnit I X Y hY).app M =
      limit.lift _ (etaleAssociatedCoefficientPowerCone I X Y hY M) := by
  apply limit.hom_ext
  intro n
  rw [limit.lift_π]
  exact (etaleAssociatedCoefficientPowerLimitUnit_π I X Y hY M n.unop).trans
    (etaleAssociatedCoefficientPowerCone_π I X Y hY M n.unop).symm

/-- Cover evaluation of the limit is the limit of the evaluated coefficient system. -/
def etaleAssociatedCoefficientPowerLimitEvaluationIso
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (j : J) :
    ((etaleAssociatedCoefficientPowerLimit I X Y hY).obj M).obj j ≅
      limit (((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M) ⋙
        (evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j) :=
  limitObjIsoLimitCompEvaluation _ j

/-- The sheaf-power limit at a cover is the existing ordinary ideal-adic limit sheaf. -/
def etaleAssociatedSheafPowerLimitEvaluationIso
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (j : J) :
    ((etaleAssociatedSheafPowerLimit I X Y hY).obj M).obj j ≅
      Langlands.Sheaf.AdicSystem.inverseLimit X.smallEtaleTopology I
        ((etaleAssociatedVaryingSystem X Y hY M).obj j) :=
  limitObjIsoLimitCompEvaluation _ j

@[reassoc (attr := simp)]
theorem etaleAssociatedCoefficientPowerLimitEvaluationIso_hom_π
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (j : J) (n : ℕ) :
    (etaleAssociatedCoefficientPowerLimitEvaluationIso I X Y hY M j).hom ≫
        limit.π _ (op n) =
      (limit.π ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M) (op n)).app j :=
  limitObjIsoLimitCompEvaluation_hom_π _ _ _

@[reassoc (attr := simp)]
theorem etaleAssociatedSheafPowerLimitEvaluationIso_hom_projection
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (j : J) (n : ℕ) :
    (etaleAssociatedSheafPowerLimitEvaluationIso I X Y hY M j).hom ≫
        Langlands.Sheaf.AdicSystem.projection X.smallEtaleTopology I
          ((etaleAssociatedVaryingSystem X Y hY M).obj j) n =
      (limit.π ((etaleAssociatedSheafPowerSystems I X Y hY).obj M) (op n)).app j :=
  limitObjIsoLimitCompEvaluation_hom_π _ _ _

/-- Evaluation carries the limit comparison to the limit of the original pointwise comparisons. -/
theorem etaleAssociatedPowerLimitComparison_evaluation
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (j : J) :
    ((etaleAssociatedPowerLimitComparison I X Y hY).app M).app j ≫
        (etaleAssociatedCoefficientPowerLimitEvaluationIso I X Y hY M j).hom =
      (etaleAssociatedSheafPowerLimitEvaluationIso I X Y hY M j).hom ≫
        limMap ((constantAssociatedReductionSystemsComparison I X (Y.action j)).app
          (M.action j)) :=
  limit.map_post ((etaleAssociatedVaryingReductionSystemsComparison I X Y hY).app M)
    ((evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j)

/-- In every cover coordinate, the completion unit still projects to the genuine quotient. -/
@[reassoc (attr := simp)]
theorem etaleAssociatedSheafPowerLimitUnit_evaluation_projection
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (j : J) (n : ℕ) :
    ((etaleAssociatedSheafPowerLimitUnit I X Y hY).app M).app j ≫
        (etaleAssociatedSheafPowerLimitEvaluationIso I X Y hY M j).hom ≫
          Langlands.Sheaf.AdicSystem.projection X.smallEtaleTopology I
            ((etaleAssociatedVaryingSystem X Y hY M).obj j) n =
      (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n).app
        ((etaleAssociatedVaryingSystem X Y hY M).obj j) := by
  rw [etaleAssociatedSheafPowerLimitEvaluationIso_hom_projection]
  exact congrArg (fun a => a.app j) (etaleAssociatedSheafPowerLimitUnit_π I X Y hY M n)

end Langlands.Shimura.Coefficients
