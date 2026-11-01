import Langlands.Shimura.Coefficients.EtaleVaryingCoverPullback
import Langlands.Shimura.Coefficients.VaryingCoverInverse

/-! # Etale base change of full varying-torsor coefficient systems -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]
variable (R : Type u) [CommRing R]
variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))

/-- The actual inverse-cover transition commutes with etale base change. -/
@[reassoc] theorem etaleAssociatedTransition_pullback {i j : I} (b : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (EtalePullback.restriction f (ModuleCat.{u} R)).map
        ((etaleAssociatedTransition X Y hY b).app M) ≫
        (etaleAssociatedAtPullback f R Y j).hom.app M =
      (etaleAssociatedAtPullback f R Y i).hom.app M ≫
        (etaleAssociatedTransition Z ((etaleTorsorDiagramPullback f D).obj Y)
          (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY) b).app M := by
  let := etaleAssociatedComparison_app_isIso Z
    ((etaleTorsorDiagramPullback f D).obj Y)
    (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY) b M
  apply (cancel_mono
    ((etaleAssociatedComparison Z ((etaleTorsorDiagramPullback f D).obj Y) b).app M)).1
  rw [Category.assoc, ← etaleAssociatedComparison_pullback,
    ← Category.assoc, ← Functor.map_comp,
    etaleAssociatedTransition_comparison, etaleAssociatedReduction_pullback,
    Category.assoc, etaleAssociatedTransition_comparison]

/-- Restriction of the entire associated coefficient-system functor is naturally
isomorphic to the functor on the independently base-changed finite torsors. -/
def etaleAssociatedVaryingSystemPullback :
    etaleAssociatedVaryingSystemFunctor (R := R) X Y hY ⋙
        (Functor.whiskeringRight I _ _).obj
          (EtalePullback.restriction f (ModuleCat.{u} R)) ≅
      etaleAssociatedVaryingSystemFunctor Z ((etaleTorsorDiagramPullback f D).obj Y)
        (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY) :=
  NatIso.ofComponents
    (fun M => NatIso.ofComponents
      (fun i => (etaleAssociatedAtPullback f R Y i).app M)
      (fun b => etaleAssociatedTransition_pullback f R Y hY b M))
    (by
      intro M N c
      apply NatTrans.ext
      funext i
      exact (etaleAssociatedAtPullback f R Y i).hom.naturality c)

/-- The forward system comparison uses the canonical associated-sheaf
comparison at every index. -/
@[simp] theorem etaleAssociatedVaryingSystemPullback_hom_app
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I) :
    ((etaleAssociatedVaryingSystemPullback f R Y hY).hom.app M).app i =
      (etaleConstantAssociatedPullback f R (Y.action i)).hom.app (M.action i) := rfl

/-- The inverse system comparison uses the inverse canonical component. -/
@[simp] theorem etaleAssociatedVaryingSystemPullback_inv_app
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I) :
    ((etaleAssociatedVaryingSystemPullback f R Y hY).inv.app M).app i =
      (etaleConstantAssociatedPullback f R (Y.action i)).inv.app (M.action i) := rfl

/-- The inverse comparison also intertwines the complete inverse-cover
transition, as a map of the original sheaf diagrams. -/
@[reassoc] theorem etaleAssociatedTransition_pullback_inv {i j : I} (b : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedTransition Z ((etaleTorsorDiagramPullback f D).obj Y)
        (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY) b).app M ≫
        (etaleAssociatedAtPullback f R Y j).inv.app M =
      (etaleAssociatedAtPullback f R Y i).inv.app M ≫
        (EtalePullback.restriction f (ModuleCat.{u} R)).map
          ((etaleAssociatedTransition X Y hY b).app M) :=
  ((etaleAssociatedVaryingSystemPullback f R Y hY).inv.app M).naturality b

end Langlands.Shimura.Coefficients
