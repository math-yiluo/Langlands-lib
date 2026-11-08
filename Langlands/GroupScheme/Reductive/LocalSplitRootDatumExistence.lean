import Langlands.AlgebraicGeometry.FlatClosedPointGeneralization
import Langlands.GroupScheme.Reductive.LocalSplitCorootTransport
import Langlands.GroupScheme.Reductive.RootDatumExistence

/-! # Constant root datum of a split fibrewise-maximal torus over a local ring -/

universe u

namespace Langlands.GroupScheme

/-- The flat lifting property holds, by the published flat generalization lemma. -/
theorem LocalSplitCorootTransport.flatClosedPointLiftProperty :
    LocalSplitCorootTransport.FlatClosedPointLiftProperty.{u} :=
  fun _ _ _ _ f _ x hx l _ _ =>
    Langlands.AlgebraicGeometry.exists_extension_point_of_flat_of_closedPoint f x hx l

/-- **Constant root datum over a local ring.** A closed coordinate split torus in a reductive
group over a local ring that is maximal on every residue-field fibre has a single finite reduced
root datum that is its root datum on every field-valued fibre. -/
theorem localSplitFibrewiseRootDatumExistence :
    LocalSplitFibrewiseRootDatumExistenceStatement.{u} :=
  localSplitFibrewiseRootDatumExistence_of_rootDatumExistence rootDatumExistence
    LocalSplitCorootTransport.flatClosedPointLiftProperty

end Langlands.GroupScheme
