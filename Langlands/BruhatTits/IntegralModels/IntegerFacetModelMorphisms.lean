import Langlands.Geometry.Building.IntegerBuildingFacetFixers
import Langlands.BruhatTits.IntegralModels.IntegerFacetParabolicImages
import Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof

/-! # Constructing actual comparison maps for supplied integer-facet models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace RelativeComponentModelHom

/-- Over a strictly Henselian DVR, inclusion of the full integral-point
images is exactly the criterion for a compatible full and neutral map. -/
theorem nonempty_iff_integralPoints_le
    (D E : RelativeComponentModelData R K G) :
    Nonempty (RelativeComponentModelHom D E) ↔
      D.full.integralPoints ≤ E.full.integralPoints := by
  constructor
  · rintro ⟨φ⟩
    exact φ.full_integralPoints_le
  · intro hle
    obtain ⟨φ⟩ := IntegralModel.smoothHomExtension R K G G (𝟙 G)
      D.full E.full D.full_smooth (fun g hg => by
        simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]
          using hle hg)
    exact ⟨ofFull φ⟩

/-- Choose an actual generic-identity full map and its canonical neutral
restriction from inclusion of the original full integral-point images. -/
def ofIntegralPointsLE (D E : RelativeComponentModelData R K G)
    (hle : D.full.integralPoints ≤ E.full.integralPoints) :
    RelativeComponentModelHom D E :=
  Classical.choice ((nonempty_iff_integralPoints_le D E).mpr hle)

end RelativeComponentModelHom

variable [IsAffineHom G.X.hom]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)
  (D : B.BuildingFacet → RelativeComponentModelData R K G)
  (hpoints : ∀ F, (D F).full.integralPoints =
    characterValuationKernel v G ⊓ B.pointwiseFixer F.val)

namespace IntegerFacetModelData

include hpoints

omit [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)] in
/-- Actual incidence reverses the full-model integral-point images, using
their supplied descriptions in the original rational-point group. -/
theorem full_integralPoints_le_of_facetPrecedes
    {F C : B.BuildingFacet} (hFC : B.FacetPrecedes F C) :
    (D C).full.integralPoints ≤ (D F).full.integralPoints := by
  rw [hpoints C, hpoints F]
  exact inf_le_inf_left _ (B.pointwiseFixer_le_of_facetPrecedes hFC)

/-- The full integral-point descriptions construct actual compatible model
maps in the opposite incidence direction. -/
def morphismOfIntegralPoints
    (F C : B.BuildingFacet) (hFC : B.FacetPrecedes F C) :
    RelativeComponentModelHom (D C) (D F) :=
  RelativeComponentModelHom.ofIntegralPointsLE (D C) (D F)
    (full_integralPoints_le_of_facetPrecedes B D hpoints hFC)

/-- Assemble the supplied models into facet model data; no comparison
morphisms are assumed as input. -/
def ofIntegralPoints : IntegerFacetModelData B R where
  model := D
  morphism := morphismOfIntegralPoints B D hpoints

@[simp] theorem ofIntegralPoints_model :
    (ofIntegralPoints B D hpoints).model = D := rfl

theorem ofIntegralPoints_full_integralPoints (F : B.BuildingFacet) :
    ((ofIntegralPoints B D hpoints).model F).full.integralPoints =
      characterValuationKernel v G ⊓ B.pointwiseFixer F.val :=
  hpoints F

/-- The constructed neutral map carries the actual neutral integral-point
image into that of the lower facet, without an additional neutral-point
description. -/
theorem neutral_integralPoints_le_of_facetPrecedes
    {F C : B.BuildingFacet} (hFC : B.FacetPrecedes F C) :
    (D C).neutral.integralPoints ≤ (D F).neutral.integralPoints :=
  (morphismOfIntegralPoints B D hpoints F C hFC).neutral_integralPoints_le

end IntegerFacetModelData

/-- Supplied smooth component models with the exact full fixer-point
descriptions assemble into actual integer-facet model data over a strictly
Henselian DVR. The individual models and their point descriptions are supplied;
their existence and residue-parabolic correspondence are not proved here. -/
def IntegerFacetModelMorphismsStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    (B : IntegerValuationBuildingData v G)
    (D : B.BuildingFacet → RelativeComponentModelData R K G),
    (∀ F, (D F).full.integralPoints =
      characterValuationKernel v G ⊓ B.pointwiseFixer F.val) →
    ∃ M : IntegerFacetModelData B R, M.model = D

theorem integerFacetModelMorphisms : IntegerFacetModelMorphismsStatement.{u} := by
  intro R K _ _ _ _ _ _ _ _ G _ v B D hpoints
  exact ⟨IntegerFacetModelData.ofIntegralPoints B D hpoints, rfl⟩

end Langlands.BruhatTits.IntegralModels
