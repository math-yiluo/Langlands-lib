import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.IntegralModel.HenselianReduction

/-! # A reduction-preimage criterion for actual model morphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)

local instance specialFibre_affine [IsLocalRing R] (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance specialFibre_isAffine [IsLocalRing R] (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

section Local

variable [IsLocalRing R]

/-- Every special-fibre image of an integral section lies in the residue points
of the schematic image, even when its projection is not rationally surjective. -/
theorem sectionRange_le_reductionPreimage :
    (rationalPoints.map φ.neutral.hom).range ≤
      φ.specialFibreImagePoints.comap target.neutral.reduction := by
  rintro _ ⟨x, rfl⟩
  refine ⟨rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap)
    (source.neutral.reduction x), ?_⟩
  rw [φ.neutral_reduction_naturality]
  change (source.neutral.reduction x ≫
    (SchematicImage.projection φ.neutralSpecialFibreMap).hom.hom) ≫
      φ.specialFibreImageInclusion.hom.hom = _
  rw [Category.assoc, ← Grp.comp_hom_hom, SchematicImage.projection_inclusion]
  rfl

/-- Surjectivity onto all original residue-field points of the schematic image
identifies these points with the range of the special-fibre homomorphism. -/
theorem specialFibreImagePoints_eq_range
    (hπ : Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap))) :
    φ.specialFibreImagePoints = (rationalPoints.map φ.neutralSpecialFibreMap).range := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := hπ z
    refine ⟨x, ?_⟩
    change x ≫ φ.neutralSpecialFibreMap.hom.hom =
      (x ≫ (SchematicImage.projection φ.neutralSpecialFibreMap).hom.hom) ≫
        φ.specialFibreImageInclusion.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, SchematicImage.projection_inclusion]
  · rintro ⟨x, rfl⟩
    refine ⟨rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap) x, ?_⟩
    change (x ≫ (SchematicImage.projection φ.neutralSpecialFibreMap).hom.hom) ≫
      φ.specialFibreImageInclusion.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, SchematicImage.projection_inclusion]
    rfl

/-- For an identity-generic-fibre model homomorphism, section-level containment
of the congruence kernel is precisely generic-point containment. -/
theorem congruenceKernel_le_sectionRange_iff :
    target.neutral.congruenceKernel ≤ (rationalPoints.map φ.neutral.hom).range ↔
      target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints := by
  constructor
  · intro h g hg
    obtain ⟨x, hx, rfl⟩ := hg
    obtain ⟨y, hy⟩ := h hx
    exact ⟨y, (φ.neutral_integralPointMap y).symm.trans
      (congrArg target.neutral.integralPointMap hy)⟩
  · intro h x hx
    obtain ⟨y, hy⟩ := h ⟨x, hx, rfl⟩
    refine ⟨y, target.neutral.integralPointMap_injective ?_⟩
    exact (φ.neutral_integralPointMap y).trans hy

end Local

section Henselian

variable [HenselianLocalRing R]

/-- Smooth Henselian reduction identifies the reduction of the section range
with the range of the original special-fibre homomorphism. -/
theorem sectionRange_map_reduction
    (hsource : source.neutral.IsSmooth) :
    (rationalPoints.map φ.neutral.hom).range.map target.neutral.reduction =
      (rationalPoints.map φ.neutralSpecialFibreMap).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨source.neutral.reduction x, (φ.neutral_reduction_naturality x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := source.neutral.reduction_surjective hsource x
    exact ⟨rationalPoints.map φ.neutral.hom z, ⟨z, rfl⟩,
      φ.neutral_reduction_naturality z⟩

/-- The full reduction preimage is the join of the integral-section image and
the target congruence kernel, under rational surjectivity onto the schematic image. -/
theorem reductionPreimage_eq_sup_congruenceKernel
    (hsource : source.neutral.IsSmooth)
    (hπ : Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap))) :
    φ.specialFibreImagePoints.comap target.neutral.reduction =
      (rationalPoints.map φ.neutral.hom).range ⊔ target.neutral.congruenceKernel := by
  rw [φ.specialFibreImagePoints_eq_range hπ,
    ← φ.sectionRange_map_reduction hsource, Subgroup.comap_map_eq]
  rfl

/-- With smooth source and rationally surjective image projection, the KP
reduction-preimage assertion is equivalent to one congruence-kernel inclusion. -/
theorem hasParabolicReductionPreimage_iff
    (hsource : source.neutral.IsSmooth)
    (hπ : Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap))) :
    φ.HasParabolicReductionPreimage ↔
      target.neutral.congruenceKernel ≤ (rationalPoints.map φ.neutral.hom).range := by
  unfold HasParabolicReductionPreimage
  rw [φ.reductionPreimage_eq_sup_congruenceKernel hsource hπ, sup_eq_left]

/-- A chosen source integral section mapping to a target section whose reduction
lies in the schematic image, under the two explicit lifting inputs. -/
def reductionPreimageLift
    (hsource : source.neutral.IsSmooth)
    (hπ : Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap)))
    (hker : target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints)
    (x : φ.specialFibreImagePoints.comap target.neutral.reduction) :
    source.neutral.integralSections :=
  Classical.choose (((φ.hasParabolicReductionPreimage_iff hsource hπ).mpr
    (φ.congruenceKernel_le_sectionRange_iff.mpr hker)).le x.property)

/-- The chosen source section maps to the given target section. -/
theorem reductionPreimageLift_spec
    (hsource : source.neutral.IsSmooth)
    (hπ : Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap)))
    (hker : target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints)
    (x : φ.specialFibreImagePoints.comap target.neutral.reduction) :
    rationalPoints.map φ.neutral.hom (φ.reductionPreimageLift hsource hπ hker x) = x :=
  Classical.choose_spec (((φ.hasParabolicReductionPreimage_iff hsource hπ).mpr
    (φ.congruenceKernel_le_sectionRange_iff.mpr hker)).le x.property)

end Henselian

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom
