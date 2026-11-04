import Langlands.GroupScheme.IntegralModelReduction
import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Supplied integral models and their relative components

This is a data interface for the two models appearing in KP Axiom 4.1.20.
It does not construct either model or identify its points with building fixers.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (G : GroupScheme (Spec (CommRingCat.of K)))

/-- The supplied smooth affine model and its supplied connected-fibre relative
component, with both generic fibres identified compatibly with the same group. -/
structure RelativeComponentModelData where
  full : IntegralModel R K G
  neutral : IntegralModel R K G
  full_smooth : full.IsSmooth
  neutral_smooth : neutral.IsSmooth
  neutral_connectedFibres : neutral.HasConnectedFibres
  inclusion : neutral.Hom full (𝟙 G)
  isRelativeComponent : IsRelativeIdentityComponent full.group inclusion.hom

namespace RelativeComponentModelData

variable {R K G} (D : RelativeComponentModelData R K G)

/-- Integral sections of the full model that factor through the neutral model. -/
def neutralSections : Subgroup D.full.integralSections :=
  (rationalPoints.map D.inclusion.hom).range

/-- This subgroup is exactly the published all-test relative-component criterion
on the actual integral-base test scheme. -/
theorem mem_neutralSections_iff (x : D.full.integralSections) :
    x ∈ D.neutralSections ↔ InRelativeIdentityComponent D.full.group x := by
  exact D.isRelativeComponent.factors_iff _ x

/-- The generic-point image of neutral sections in the original generic group. -/
def neutralPoints : Subgroup (rationalPoints G) :=
  D.neutralSections.map D.full.integralPointMap

/-- Compatible generic identifications identify this image with the neutral
model's own integral-point image. -/
theorem neutralPoints_eq :
    D.neutralPoints = D.neutral.integralPoints := by
  ext g
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨y, ?_⟩
    have h := D.inclusion.integralPointMap_naturality y
    simpa [rationalPoints.map] using h.symm
  · rintro ⟨y, rfl⟩
    refine ⟨rationalPoints.map D.inclusion.hom y, ⟨y, rfl⟩, ?_⟩
    have h := D.inclusion.integralPointMap_naturality y
    simpa [rationalPoints.map] using h

/-- Membership can be expressed without choosing a section of the neutral model. -/
theorem mem_neutralPoints_iff (g : rationalPoints G) :
    g ∈ D.neutralPoints ↔
      ∃ x : D.full.integralSections,
        InRelativeIdentityComponent D.full.group x ∧ D.full.integralPointMap x = g := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, (D.mem_neutralSections_iff x).mp hx, h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, (D.mem_neutralSections_iff x).mpr hx, h⟩

/-- The neutral generic-point image lies in the full model's integral-point image. -/
theorem neutralPoints_le_full :
    D.neutralPoints ≤ D.full.integralPoints := by
  rintro g ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

section Residue

variable [IsLocalRing R]

/-- The inclusion of models induces the actual map between their full special fibres. -/
def specialFibreMap : D.neutral.specialFibre ⟶ D.full.specialFibre :=
  D.inclusion.specialFibreMap

/-- Reduction of neutral-model sections commutes with the model inclusion. -/
theorem reduction_naturality (x : D.neutral.integralSections) :
    D.full.reduction (rationalPoints.map D.inclusion.hom x) =
      rationalPoints.map D.specialFibreMap (D.neutral.reduction x) :=
  D.inclusion.reduction_naturality x

/-- The congruence kernel maps into the full model's congruence kernel. -/
theorem map_mem_congruenceKernel {x : D.neutral.integralSections}
    (hx : x ∈ D.neutral.congruenceKernel) :
    rationalPoints.map D.inclusion.hom x ∈ D.full.congruenceKernel :=
  D.inclusion.map_mem_congruenceKernel hx

end Residue
end RelativeComponentModelData
end Langlands.BruhatTits.IntegralModels
