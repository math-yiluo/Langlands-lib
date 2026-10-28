import Langlands.Shimura.Coefficients.VaryingCoverInverse
import Langlands.Shimura.Coefficients.VaryingCoverReduction

/-! # Coefficient-power systems of associated sheaf diagrams -/

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

/-- Associate sheaf diagrams to all actual coefficient powers. -/
def etaleAssociatedCoefficientPowerSystems :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (ℕᵒᵖ ⥤ (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) :=
  coefficientDiagramReductionFunctor I ⋙
    (Functor.whiskeringRight ℕᵒᵖ
      (EquivariantDiagram D (ModuleCat.{u} R))
      (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj
        (etaleAssociatedVaryingSystemFunctor X Y hY)

/-- Quotient the original associated sheaf diagram at every power. -/
def etaleAssociatedSheafPowerSystems :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (ℕᵒᵖ ⥤ (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) :=
  etaleAssociatedVaryingSystemFunctor X Y hY ⋙
    (Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I ⋙
      Functor.whiskeringRight J
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).flip

/-- The pointwise comparison unit is the actual associated-diagram quotient map. -/
@[reassoc]
theorem etaleAssociatedVaryingPowerUnit_app
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) (j : J) :
    (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n).app
        ((etaleAssociatedVaryingSystem X Y hY M).obj j) ≫
      (constantAssociatedPowerReductionComparison I X (Y.action j) n).app
        (M.action j) =
      ((etaleAssociatedVaryingSystemFunctor X Y hY).map
        ((coefficientDiagramPowerUnit I n).app M)).app j :=
  constantAssociatedPowerReductionComparison_unit I X (Y.action j) n (M.action j)

/-- The canonical power comparison is natural across the varying covers. -/
def etaleAssociatedVaryingPowerComparison
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    ((etaleAssociatedSheafPowerSystems I X Y hY).obj M).obj (op n) ⟶
      ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M).obj (op n) where
  app j := (constantAssociatedPowerReductionComparison I X (Y.action j) n).app
    (M.action j)
  naturality {i j} f := by
    apply (cancel_epi
      ((Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n).app
        ((etaleAssociatedVaryingSystem X Y hY M).obj i))).mp
    have hq := (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n).naturality
      ((etaleAssociatedVaryingSystem X Y hY M).map f)
    simp only [CategoryTheory.Functor.id_map] at hq
    rw [← Category.assoc]
    erw [← hq]
    rw [Category.assoc]
    rw [etaleAssociatedVaryingPowerUnit_app,
      etaleAssociatedVaryingPowerUnit_app_assoc]
    exact ((etaleAssociatedVaryingSystemFunctor X Y hY).map
      ((coefficientDiagramPowerUnit I n).app M)).naturality f

/-- The canonical comparisons respect both powers and coefficient diagrams. -/
def etaleAssociatedVaryingReductionSystemsComparison :
    etaleAssociatedSheafPowerSystems I X Y hY ⟶
      etaleAssociatedCoefficientPowerSystems I X Y hY where
  app M :=
    { app n := etaleAssociatedVaryingPowerComparison I X Y hY M n.unop
      naturality {_m _n} f := by
        apply NatTrans.ext
        funext j
        exact congrArg (fun a => a.app (M.action j))
          (constantAssociatedPowerReductionComparison_transition I X (Y.action j)
            (leOfHom f.unop)) }
  naturality {M N} c := by
    apply NatTrans.ext
    funext n
    apply NatTrans.ext
    funext j
    exact (constantAssociatedPowerReductionComparison I X (Y.action j) n.unop).naturality
      ((EquivariantDiagram.evaluation j).map c)

/-- The comparison carries the genuine quotient unit on the whole cover diagram. -/
theorem etaleAssociatedVaryingReductionSystemsComparison_unit
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    Functor.whiskerLeft (etaleAssociatedVaryingSystem X Y hY M)
        (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n) ≫
      ((etaleAssociatedVaryingReductionSystemsComparison I X Y hY).app M).app (op n) =
        (etaleAssociatedVaryingSystemFunctor X Y hY).map
          ((coefficientDiagramPowerUnit I n).app M) := by
  apply NatTrans.ext
  funext j
  exact constantAssociatedPowerReductionComparison_unit I X (Y.action j) n (M.action j)

@[simp] theorem etaleAssociatedCoefficientPowerSystems_obj
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) (j : J) :
    (((etaleAssociatedCoefficientPowerSystems I X Y hY).obj M).obj (op n)).obj j =
      (etaleAssociatedFunctor X (Y.action j)).obj
        ((((Langlands.Coefficients.AdicSystem.powerReduction I n).mapAction
          (D.obj j)).obj (M.action j))) := rfl

@[simp] theorem etaleAssociatedSheafPowerSystems_obj
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) (j : J) :
    (((etaleAssociatedSheafPowerSystems I X Y hY).obj M).obj (op n)).obj j =
      ((Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I).obj (op n)).obj
        ((etaleAssociatedFunctor X (Y.action j)).obj (M.action j)) := rfl

@[simp] theorem etaleAssociatedVaryingReductionSystemsComparison_app
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) (j : J) :
    (((etaleAssociatedVaryingReductionSystemsComparison I X Y hY).app M).app
        (op n)).app j =
      (constantAssociatedPowerReductionComparison I X (Y.action j) n).app (M.action j) :=
  rfl

end Langlands.Shimura.Coefficients
