import Langlands.BruhatTits.IntegralModels.FacetParabolicOrder
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.IntegralModel.SmoothIntersection
import Langlands.GroupScheme.SchematicImageComparison
import Langlands.GroupScheme.Absolute.ParabolicTransport

/-! # Incidence and the actual special-fibre images of facet models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace RelativeComponentModelHom

/-- Identity generic fibres force compatibility of the neutral maps with composition. -/
theorem neutral_hom_comp
    {D₀ D₁ D₂ : RelativeComponentModelData R K G}
    (φ : RelativeComponentModelHom D₂ D₁)
    (ψ : RelativeComponentModelHom D₁ D₀)
    (χ : RelativeComponentModelHom D₂ D₀) :
    φ.neutral.hom ≫ ψ.neutral.hom = χ.neutral.hom := by
  let c : D₂.neutral.Hom D₀.neutral (𝟙 G) :=
    { hom := φ.neutral.hom ≫ ψ.neutral.hom
      generic_comm := by
        simpa only [IntegralModel.Hom.comp, Category.id_comp] using
          (φ.neutral.comp ψ.neutral).generic_comm }
  exact c.hom_eq χ.neutral

/-- The actual residue base changes inherit the forced composition identity. -/
theorem neutralSpecialFibreMap_comp [IsLocalRing R]
    {D₀ D₁ D₂ : RelativeComponentModelData R K G}
    (φ : RelativeComponentModelHom D₂ D₁)
    (ψ : RelativeComponentModelHom D₁ D₀)
    (χ : RelativeComponentModelHom D₂ D₀) :
    φ.neutralSpecialFibreMap ≫ ψ.neutralSpecialFibreMap =
      χ.neutralSpecialFibreMap := by
  simpa only [neutralSpecialFibreMap, IntegralModel.Hom.specialFibreMap, Functor.map_comp] using
    congrArg ((baseChange (IntegralModel.residueBaseMap R)).map)
      (φ.neutral_hom_comp ψ χ)

end RelativeComponentModelHom

private instance incidence_neutralSpecialFibre_affine [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

private instance incidence_neutralSpecialFibre_isAffine [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

/-- A further source factor can only shrink the actual closed schematic image. -/
private theorem schematicImage_range_le_of_factor
    {k : Type u} [Field k]
    {A B H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom]
    (p : A ⟶ B) (f : B ⟶ H) (g : A ⟶ H)
    [QuasiCompact f.hom.hom.left] [QuasiCompact g.hom.hom.left] (h : p ≫ f = g) :
    SubgroupFunctor.range (SchematicImage.inclusion g) ≤
      SubgroupFunctor.range (SchematicImage.inclusion f) := by
  apply (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant
    (SchematicImage.projection g) (SchematicImage.inclusion g)
    (SchematicImage.inclusion f)
    (inferInstanceAs (IsClosedImmersion (SchematicImage.inclusion f).hom.hom.left))).mp
  rw [SchematicImage.projection_inclusion]
  exact SubgroupFunctor.range_le_of_factor (p ≫ SchematicImage.projection f) (by
    rw [Category.assoc, SchematicImage.projection_inclusion, h])

namespace FacetModelData

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [IsAffineHom G.X.hom] {B : ValuationBuildingData G} [IsLocalRing R]
  (M : FacetModelData B R) (F : BuildingFacet B)

/-- The all-test subgroup represented by the actual neutral special-fibre image
of an incident facet's model morphism. -/
def incidentSpecialFibreImage (F' : IncidentFacets B F) :
    SubgroupFunctor (M.model F).neutral.specialFibre :=
  SubgroupFunctor.range
    ((M.morphism F F'.val F'.property).specialFibreImageInclusion)

/-- Increasing incident facets give decreasing actual neutral special-fibre images. -/
theorem incidentSpecialFibreImage_le
    (F₁ F₂ : IncidentFacets B F) (h : FacetPrecedes B F₁.val F₂.val) :
    M.incidentSpecialFibreImage F F₂ ≤ M.incidentSpecialFibreImage F F₁ := by
  have : IsAffine (M.model F).neutral.specialFibre.X.left :=
    isAffine_of_isAffineHom (M.model F).neutral.specialFibre.X.hom
  have : IsAffine (M.model F₁.val).neutral.specialFibre.X.left :=
    isAffine_of_isAffineHom (M.model F₁.val).neutral.specialFibre.X.hom
  have : IsAffine (M.model F₂.val).neutral.specialFibre.X.left :=
    isAffine_of_isAffineHom (M.model F₂.val).neutral.specialFibre.X.hom
  have : IsAffineHom (M.morphism F F₁.val F₁.property).neutralSpecialFibreMap.hom.hom.left :=
    isAffineHom_of_isAffine _
  have : IsAffineHom (M.morphism F F₂.val F₂.property).neutralSpecialFibreMap.hom.hom.left :=
    isAffineHom_of_isAffine _
  have : QuasiCompact
      (M.morphism F F₁.val F₁.property).neutralSpecialFibreMap.hom.hom.left := by
    exact quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU => (hU.preimage _).isCompact
  have : QuasiCompact
      (M.morphism F F₂.val F₂.property).neutralSpecialFibreMap.hom.hom.left := by
    exact quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU => (hU.preimage _).isCompact
  exact schematicImage_range_le_of_factor
    (M.morphism F₁.val F₂.val h).neutralSpecialFibreMap
    (M.morphism F F₁.val F₁.property).neutralSpecialFibreMap
    (M.morphism F F₂.val F₂.property).neutralSpecialFibreMap
    (RelativeComponentModelHom.neutralSpecialFibreMap_comp _ _ _)

/-- Increasing incident facets give decreasing actual images in any supplied quotient.
No parabolicity or reductivity hypothesis is needed for this order direction. -/
theorem incidentParabolicImage_le (Q : SpecialFibreQuotientData (M.model F))
    (F₁ F₂ : IncidentFacets B F) (h : FacetPrecedes B F₁.val F₂.val) :
    M.incidentParabolicImage F Q F₂ ≤ M.incidentParabolicImage F Q F₁ := by
  have : IsAffine Q.quotient.X.left := isAffine_of_isAffineHom Q.quotient.X.hom
  apply schematicImage_range_le_of_factor
    (M.morphism F₁.val F₂.val h).neutralSpecialFibreMap
    ((M.morphism F F₁.val F₁.property).neutralSpecialFibreMap ≫ Q.projection)
    ((M.morphism F F₂.val F₂.property).neutralSpecialFibreMap ≫ Q.projection)
  rw [← Category.assoc, RelativeComponentModelHom.neutralSpecialFibreMap_comp]

end FacetModelData
end Langlands.BruhatTits.IntegralModels
