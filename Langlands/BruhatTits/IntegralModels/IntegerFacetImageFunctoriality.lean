import Langlands.BruhatTits.IntegralModels.IntegerFacetParabolicImages
import Langlands.Geometry.Building.IntegerBuildingFacetOrder
import Langlands.GroupScheme.SchematicImageFunctoriality

/-! # Composition and opposite inclusion for actual integer-facet residue images -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.Geometry.Building

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  {B : IntegerValuationBuildingData v G}
  {R : Type u} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]

namespace IntegerFacetModelData

variable (M : IntegerFacetModelData B R)

/-- Generic identity makes the neutral incidence maps automatically coherent. -/
theorem neutralMap_comp {F C D : B.BuildingFacet}
    (hFC : B.FacetPrecedes F C) (hCD : B.FacetPrecedes C D) :
    (M.morphism F D (B.facetPrecedes_trans hFC hCD)).neutral.hom =
      (M.morphism C D hCD).neutral.hom ≫ (M.morphism F C hFC).neutral.hom := by
  apply IntegralModel.hom_eq_of_generic
  apply (cancel_mono (M.model F).neutral.genericIso.hom).mp
  rw [(M.morphism F D (B.facetPrecedes_trans hFC hCD)).neutral.generic_comm,
    Functor.map_comp, Category.assoc, (M.morphism F C hFC).neutral.generic_comm,
    ← Category.assoc, (M.morphism C D hCD).neutral.generic_comm]
  simp

variable [IsLocalRing R]

local instance imageFunctoriality_neutralAffine (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance imageFunctoriality_neutralIsAffine (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

local instance imageFunctoriality_quotientIsAffine {D : RelativeComponentModelData R K G}
    (Q : SpecialFibreQuotientData D) : IsAffine Q.quotient.X.left :=
  isAffine_of_isAffineHom Q.quotient.X.hom

/-- The actual neutral special-fibre maps inherit composition from the models. -/
theorem neutralSpecialFibreMap_comp {F C D : B.BuildingFacet}
    (hFC : B.FacetPrecedes F C) (hCD : B.FacetPrecedes C D) :
    (M.morphism F D (B.facetPrecedes_trans hFC hCD)).neutralSpecialFibreMap =
      (M.morphism C D hCD).neutralSpecialFibreMap ≫
        (M.morphism F C hFC).neutralSpecialFibreMap := by
  change (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map _ =
    (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map _ ≫
      (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map _
  rw [M.neutralMap_comp hFC hCD, Functor.map_comp]

variable (F : B.BuildingFacet) (Q : SpecialFibreQuotientData (M.model F))

/-- Original facet incidence reverses containment of actual residue images.
No parabolicity or coherence premise is needed. -/
theorem incidentParabolicImage_le {F₁ F₂ : B.IncidentFacets F}
    (h : B.FacetPrecedes F₁.val F₂.val) :
    M.incidentParabolicImage F Q F₂ ≤ M.incidentParabolicImage F Q F₁ := by
  change SubgroupFunctor.range
      (SchematicImage.inclusion
        ((M.morphism F F₂.val F₂.property).neutralSpecialFibreMap ≫ Q.projection)) ≤
    SubgroupFunctor.range
      (SchematicImage.inclusion
        ((M.morphism F F₁.val F₁.property).neutralSpecialFibreMap ≫ Q.projection))
  rw [M.neutralSpecialFibreMap_comp F₁.property h, Category.assoc]
  exact SchematicImage.range_inclusion_comp_le _ _

/-- The opposite inclusion clause in the facet-parabolic correspondence is
automatic for the actual model maps. Only the bijection remains to be proved. -/
theorem hasFacetParabolicOrderBijection_iff_bijOn :
    M.HasFacetParabolicOrderBijection F Q ↔
      Set.BijOn (M.incidentParabolicImage F Q) Set.univ
        {P | IsParabolicFunctor P} :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ h' => M.incidentParabolicImage_le F Q h'⟩⟩

/-- Composition of actual neutral maps, reversed image containment, and the
resulting simplification of the remaining parabolic-bijection obligation. -/
def ImageFunctorialityStatement : Prop :=
  (∀ (F C D : B.BuildingFacet) (hFC : B.FacetPrecedes F C)
    (hCD : B.FacetPrecedes C D),
    (M.morphism F D (B.facetPrecedes_trans hFC hCD)).neutralSpecialFibreMap =
      (M.morphism C D hCD).neutralSpecialFibreMap ≫
        (M.morphism F C hFC).neutralSpecialFibreMap) ∧
  (∀ F₁ F₂ : B.IncidentFacets F, B.FacetPrecedes F₁.val F₂.val →
    M.incidentParabolicImage F Q F₂ ≤ M.incidentParabolicImage F Q F₁) ∧
  (M.HasFacetParabolicOrderBijection F Q ↔
    Set.BijOn (M.incidentParabolicImage F Q) Set.univ {P | IsParabolicFunctor P})

theorem imageFunctoriality : M.ImageFunctorialityStatement F Q :=
  ⟨fun _ _ _ => M.neutralSpecialFibreMap_comp,
    fun _ _ => M.incidentParabolicImage_le F Q,
    M.hasFacetParabolicOrderBijection_iff_bijOn F Q⟩

end IntegerFacetModelData
end Langlands.BruhatTits.IntegralModels
