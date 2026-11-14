import Langlands.Geometry.Building.IntegerBuildingFacetClosure
import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Actual residue images of incident integer-valued building facets -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.Geometry.Building

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)
  (R : Type u) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]

/-- Supplied models of the original full facets over an arbitrary integer-valued
field, with actual generic-identity comparisons in the incidence direction. -/
structure IntegerFacetModelData where
  model : B.BuildingFacet → RelativeComponentModelData R K G
  morphism : ∀ (F F' : B.BuildingFacet), B.FacetPrecedes F F' →
    RelativeComponentModelHom (model F') (model F)

namespace IntegerFacetModelData

variable {B R} [IsLocalRing R] (M : IntegerFacetModelData B R)
  (F : B.BuildingFacet) (Q : SpecialFibreQuotientData (M.model F))

local instance neutralSpecialFibre_affine (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance neutralSpecialFibre_isAffine (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

local instance quotient_isAffine {D : RelativeComponentModelData R K G}
    (Q : SpecialFibreQuotientData D) : IsAffine Q.quotient.X.left :=
  isAffine_of_isAffineHom Q.quotient.X.hom

/-- The all-test range of the actual schematic-image inclusion into the
specified neutral special-fibre quotient. -/
def incidentParabolicImage (F' : B.IncidentFacets F) : SubgroupFunctor Q.quotient :=
  SubgroupFunctor.range
    ((M.morphism F F'.val F'.property).reductiveImageInclusion Q)

/-- The complete facet-to-parabolic bijection and its original opposite
inclusion direction, on the actual integer-valued building. -/
def HasFacetParabolicOrderBijection : Prop :=
  Set.BijOn (M.incidentParabolicImage F Q) Set.univ
    {P | IsParabolicFunctor P} ∧
      ∀ F₁ F₂ : B.IncidentFacets F, B.FacetPrecedes F₁.val F₂.val →
        M.incidentParabolicImage F Q F₂ ≤ M.incidentParabolicImage F Q F₁

variable {M F Q}

theorem HasFacetParabolicOrderBijection.isParabolic
    (h : M.HasFacetParabolicOrderBijection F Q) (F' : B.IncidentFacets F) :
    IsParabolicFunctor (M.incidentParabolicImage F Q F') :=
  h.1.mapsTo (Set.mem_univ F')

theorem HasFacetParabolicOrderBijection.injective
    (h : M.HasFacetParabolicOrderBijection F Q) :
    Function.Injective (M.incidentParabolicImage F Q) :=
  fun _ _ heq => h.1.injOn (Set.mem_univ _) (Set.mem_univ _) heq

theorem HasFacetParabolicOrderBijection.surjective
    (h : M.HasFacetParabolicOrderBijection F Q)
    (P : SubgroupFunctor Q.quotient) (hP : IsParabolicFunctor P) :
    ∃ F' : B.IncidentFacets F, M.incidentParabolicImage F Q F' = P := by
  obtain ⟨F', _, hF'⟩ := h.1.surjOn hP
  exact ⟨F', hF'⟩

variable (M F)

/-- A generic-identity comparison from a model to itself is the actual identity
also on the neutral special fibre. No coherence field is assumed. -/
theorem neutralSpecialFibreMap_self :
    (M.morphism F F (B.facetPrecedes_refl F)).neutralSpecialFibreMap =
      𝟙 (M.model F).neutral.specialFibre := by
  let e : (M.model F).neutral.Hom (M.model F).neutral (𝟙 G) :=
    ⟨𝟙 _, by simp⟩
  have he := (M.morphism F F (B.facetPrecedes_refl F)).neutral.hom_eq e
  change (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map _ = _
  rw [he]
  exact CategoryTheory.Functor.map_id _ _

variable (Q)

/-- The facet itself maps to the whole reductive quotient. The argument uses
scheme surjectivity of the fppf quotient and reducedness of its actual target,
not surjectivity of quotient maps on every original test-point group. -/
theorem incidentParabolicImage_self (hQ : Q.IsReductiveQuotient) :
    M.incidentParabolicImage F Q ⟨F, B.facetPrecedes_refl F⟩ = ⊤ := by
  let f := (M.morphism F F (B.facetPrecedes_refl F)).neutralSpecialFibreMap ≫
    Q.projection
  have hf : f = Q.projection := by
    dsimp [f]
    rw [M.neutralSpecialFibreMap_self F, Category.id_comp]
  have : Surjective f.hom.hom.left := by
    rw [hf]
    exact hQ.2.1.2.1
  have hfac := congrArg (fun a => a.hom.hom.left)
    (SchematicImage.projection_inclusion f)
  have : Surjective ((SchematicImage.projection f).hom.hom.left ≫
      (SchematicImage.inclusion f).hom.hom.left) := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, hfac]
    infer_instance
  have : Surjective (SchematicImage.inclusion f).hom.hom.left :=
    Surjective.of_comp (SchematicImage.projection f).hom.hom.left
      (SchematicImage.inclusion f).hom.hom.left
  have : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  have : IsReduced Q.quotient.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (IsLocalRing.ResidueField R) _ Q.quotient.X.hom
  have : IsIso (SchematicImage.inclusion f).hom.hom.left :=
    isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map (SchematicImage.inclusion f).hom.hom) := by
    change IsIso (SchematicImage.inclusion f).hom.hom.left
    infer_instance
  have : IsIso (SchematicImage.inclusion f).hom.hom :=
    isIso_of_reflects_iso _ (Over.forget _)
  let e : SchematicImage.image f ≅ Q.quotient :=
    Grp.mkIso' (asIso (SchematicImage.inclusion f).hom.hom)
  change SubgroupFunctor.range e.hom = ⊤
  calc
    _ = SubgroupFunctor.range (e.hom ≫ 𝟙 _) := by simp
    _ = SubgroupFunctor.range (𝟙 _) := SubgroupFunctor.range_iso_comp e _
    _ = ⊤ := (SubgroupFunctor.top_isRepresentedBy_id _).2

/-- The actual neutral special-fibre self-map is the identity and its image in
an actual reductive quotient is the whole quotient. -/
def IntegerFacetParabolicImagesStatement : Prop :=
  (M.morphism F F (B.facetPrecedes_refl F)).neutralSpecialFibreMap =
      𝟙 (M.model F).neutral.specialFibre ∧
    (Q.IsReductiveQuotient →
      M.incidentParabolicImage F Q ⟨F, B.facetPrecedes_refl F⟩ = ⊤)

theorem integerFacetParabolicImages :
    M.IntegerFacetParabolicImagesStatement F Q :=
  ⟨M.neutralSpecialFibreMap_self F, M.incidentParabolicImage_self F Q⟩

end IntegerFacetModelData
end Langlands.BruhatTits.IntegralModels
