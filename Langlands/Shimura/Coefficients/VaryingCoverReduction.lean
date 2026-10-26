import Langlands.CategoryTheory.EquivariantDiagramFunctor
import Langlands.Shimura.Coefficients.VaryingCover
import Langlands.Shimura.Coefficients.CrossCoverReduction

/-! # Power-reduction systems of varying-cover coefficient cospans -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {J : Type uI} [Category.{vI} J] {D : J ⥤ GrpCat.{u}}

/-- Actual power reduction at every coefficient index, preserving varying actions. -/
def coefficientDiagramPowers :
    ℕᵒᵖ ⥤
      (EquivariantDiagram D (ModuleCat.{u} R) ⥤
        EquivariantDiagram D (ModuleCat.{u} R)) :=
  Langlands.Coefficients.AdicSystem.powers I ⋙ EquivariantDiagram.postcompose

/-- The canonical quotient transformation on the whole coefficient diagram. -/
def coefficientDiagramPowerUnit (n : ℕ) :
    𝟭 (EquivariantDiagram D (ModuleCat.{u} R)) ⟶
      (coefficientDiagramPowers I).obj (op n) :=
  EquivariantDiagram.mapNatTrans (Langlands.Coefficients.AdicSystem.quotientMap I n)

/-- Quotient units commute with the actual coefficient-power transitions. -/
@[reassoc (attr := simp)]
theorem coefficientDiagramPowerUnit_transition {m n : ℕ} (h : m ≤ n) :
    coefficientDiagramPowerUnit (D := D) I n ≫
        (coefficientDiagramPowers I).map (homOfLE h).op =
      coefficientDiagramPowerUnit I m := by
  apply NatTrans.ext
  funext M
  apply EquivariantDiagram.Hom.ext
  apply NatTrans.ext
  funext j
  exact congrArg (fun a => a.app (M.obj.obj j))
    (Langlands.Coefficients.AdicSystem.quotientMap_transition I h)

/-- All powers form an inverse system, functorial in the coefficient diagram. -/
def coefficientDiagramReductionFunctor :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (ℕᵒᵖ ⥤ EquivariantDiagram D (ModuleCat.{u} R)) :=
  (coefficientDiagramPowers I).flip

/-- Every power transition is surjective on the module at each group index. -/
theorem coefficientDiagramPowerTransition_surjective
    (M : EquivariantDiagram D (ModuleCat.{u} R))
    {m n : ℕ} (h : m ≤ n) (j : J) :
    Function.Surjective
      ((((coefficientDiagramPowers I).map (homOfLE h).op).app M).hom.app j) :=
  Langlands.Coefficients.AdicSystem.transition_surjective I h (M.obj.obj j)

variable (X : Scheme.{u}) (Y : EquivariantDiagram D X.Etale)

/-- The associated cospan at every coefficient power, with its genuine transitions. -/
def etaleAssociatedCoefficientPowerCospans {i j : J} (f : i ⟶ j) :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (ℕᵒᵖ ⥤ (WalkingCospan ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) :=
  coefficientDiagramReductionFunctor I ⋙
    (Functor.whiskeringRight ℕᵒᵖ
      (EquivariantDiagram D (ModuleCat.{u} R))
      (WalkingCospan ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj
        (etaleAssociatedTransitionCospan X Y f)

/-- Apply actual sheaf power reductions to all vertices and legs of the cospan. -/
def etaleAssociatedSheafPowerCospans {i j : J} (f : i ⟶ j) :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (ℕᵒᵖ ⥤ (WalkingCospan ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) :=
  etaleAssociatedTransitionCospan X Y f ⋙
    (Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I ⋙
      Functor.whiskeringRight WalkingCospan
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).flip

/-- The canonical reduction comparison is a genuine map of associated cospans. -/
def etaleAssociatedPowerCospanComparison {i j : J} (f : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    ((etaleAssociatedSheafPowerCospans I X Y f).obj M).obj (op n) ⟶
      ((etaleAssociatedCoefficientPowerCospans I X Y f).obj M).obj (op n) :=
  cospanHomMk
    ((constantAssociatedPowerReductionComparison I X (Y.action i) n).app
      ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j)))
    ((constantAssociatedPowerReductionComparison I X (Y.action i) n).app (M.action i))
    ((constantAssociatedPowerReductionComparison I X (Y.action j) n).app (M.action j))
    ((constantAssociatedPowerReductionComparison I X (Y.action i) n).naturality
      (M.transition f))
    (by
      change
        ((Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I).obj (op n)).map
          (etaleCrossCoverMap X (D.map f).hom (Y.transition f)
            (𝟙 ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j)))) ≫
          (constantAssociatedPowerReductionComparison I X (Y.action i) n).app
            ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j)) =
        (constantAssociatedPowerReductionComparison I X (Y.action j) n).app (M.action j) ≫
          etaleCrossCoverMap X (D.map f).hom (Y.transition f)
            (𝟙 ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj
              (((Langlands.Coefficients.AdicSystem.powerReduction I n).mapAction
                (D.obj j)).obj (M.action j))))
      have h := constantAssociatedPowerReductionComparison_crossCover I X
        (D.map f).hom (Y.transition f) n
        (𝟙 ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j)))
      rw [h]
      congr 2
      apply Action.hom_injective
      exact (Langlands.Coefficients.AdicSystem.powerReduction I n).map_id _)

/-- The cospan comparisons commute with power transitions and coefficient maps. -/
def etaleAssociatedCospanReductionSystemsComparison {i j : J} (f : i ⟶ j) :
    etaleAssociatedSheafPowerCospans I X Y f ⟶
      etaleAssociatedCoefficientPowerCospans I X Y f where
  app M :=
    { app n := etaleAssociatedPowerCospanComparison I X Y f M n.unop
      naturality m n t := by
        apply NatTrans.ext
        funext w
        rcases w with (_ | _ | _)
        · exact congrArg
            (fun a => a.app
              ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j)))
            (constantAssociatedPowerReductionComparison_transition I X (Y.action i)
              (leOfHom t.unop))
        · exact congrArg (fun a => a.app (M.action i))
            (constantAssociatedPowerReductionComparison_transition I X (Y.action i)
              (leOfHom t.unop))
        · exact congrArg (fun a => a.app (M.action j))
            (constantAssociatedPowerReductionComparison_transition I X (Y.action j)
              (leOfHom t.unop)) }
  naturality {M N} c := by
    apply NatTrans.ext
    funext n
    apply NatTrans.ext
    funext w
    rcases w with (_ | _ | _)
    · exact (constantAssociatedPowerReductionComparison I X (Y.action i) n.unop).naturality
        ((Action.res (ModuleCat.{u} R) (D.map f).hom).map
          ((EquivariantDiagram.evaluation j).map c))
    · exact (constantAssociatedPowerReductionComparison I X (Y.action i) n.unop).naturality
        ((EquivariantDiagram.evaluation i).map c)
    · exact (constantAssociatedPowerReductionComparison I X (Y.action j) n.unop).naturality
        ((EquivariantDiagram.evaluation j).map c)

@[simp] theorem etaleAssociatedCospanReductionSystemsComparison_left
    {i j : J} (f : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    (((etaleAssociatedCospanReductionSystemsComparison I X Y f).app M).app (op n)).app
        WalkingCospan.left =
      (constantAssociatedPowerReductionComparison I X (Y.action i) n).app (M.action i) := rfl

@[simp] theorem etaleAssociatedCospanReductionSystemsComparison_right
    {i j : J} (f : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    (((etaleAssociatedCospanReductionSystemsComparison I X Y f).app M).app (op n)).app
        WalkingCospan.right =
      (constantAssociatedPowerReductionComparison I X (Y.action j) n).app (M.action j) := rfl

@[simp] theorem etaleAssociatedCospanReductionSystemsComparison_one
    {i j : J} (f : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) (n : ℕ) :
    (((etaleAssociatedCospanReductionSystemsComparison I X Y f).app M).app (op n)).app
        WalkingCospan.one =
      (constantAssociatedPowerReductionComparison I X (Y.action i) n).app
        ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j)) := rfl

end Langlands.Shimura.Coefficients
