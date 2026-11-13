import Langlands.GroupScheme.IntegralModelReduction
import Langlands.Geometry.Building.KPApartment

/-! # Supplied smooth connected models of one root-filtration subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {ω : Kˣ → ℝ}
  (C : KPApartmentData i ω) (x : C.Apartment) (a : relativeRoots i) (r : ℝ)

/-- Supplied geometric data for one root-filtration group: an actual all-test
root representative, a smooth affine model with geometrically connected fibres,
and its exact specified image inside the ambient generic point group.
No existence of these data, integral root-subgroup identity, or ambient model
map is asserted by this structure. -/
structure RootFiltrationModelData where
  rootGroup : GroupScheme (Spec (CommRingCat.of K))
  inclusion : rootGroup ⟶ G
  isRootSubgroup : (RelativeRoot.subgroup i a).IsRepresentedBy inclusion
  model : IntegralModel R K rootGroup
  smooth : model.IsSmooth
  geometricallyConnected : model.HasGeometricallyConnectedFibres
  integralPoints_eq : model.integralPoints.map (rationalPoints.map inclusion) =
    C.filtration x a r

namespace RootFiltrationModelData

variable {R K C x a r}
  (U : RootFiltrationModelData R K C x a r)

/-- A compatible map into an ambient integral model places this exact
filtration subgroup inside that model's integral points. -/
theorem filtration_le_integralPoints (N : IntegralModel R K G)
    (φ : U.model.Hom N U.inclusion) : C.filtration x a r ≤ N.integralPoints := by
  rw [← U.integralPoints_eq]
  rintro g ⟨h, hh, rfl⟩
  exact φ.map_mem_integralPoints hh

end RootFiltrationModelData

end Langlands.BruhatTits.IntegralModels
