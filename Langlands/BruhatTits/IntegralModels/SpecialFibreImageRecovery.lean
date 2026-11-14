import Langlands.BruhatTits.IntegralModels.ReductionPreimage
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Recovering integral-point order from actual special-fibre images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

private instance recovery_specialFibre_affine [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

private instance recovery_specialFibre_isAffine [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

private instance recovery_specialFibre_smooth [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    Smooth D.neutral.specialFibre.X.hom := by
  have : Smooth D.neutral.group.X.hom := D.neutral_smooth
  change Smooth (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

private instance recovery_specialFibre_finiteType [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    LocallyOfFiniteType D.neutral.specialFibre.X.hom :=
  inferInstance

private instance recovery_specialFibre_connected [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    ConnectedSpace D.neutral.specialFibre.X.left :=
  D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres

variable {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)

/-- The section image is exactly the inverse image of the generic integral-point
subgroup under the target's injective generic-point map. -/
theorem sectionRange_eq_comap_integralPoints :
    (rationalPoints.map φ.neutral.hom).range =
      source.neutral.integralPoints.comap target.neutral.integralPointMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (φ.neutral_integralPointMap y).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, target.neutral.integralPointMap_injective
      ((φ.neutral_integralPointMap y).trans hy)⟩

/-- The neutral integral-section map is injective because its generic map is
the identity. -/
theorem neutralSectionMap_injective :
    Function.Injective (rationalPoints.map φ.neutral.hom) := by
  intro x y h
  apply source.neutral.integralPointMap_injective
  exact (φ.neutral_integralPointMap x).symm.trans
    ((congrArg target.neutral.integralPointMap h).trans
      (φ.neutral_integralPointMap y))

/-- Images of source sections in one target have the same order as their
generic integral-point subgroups. -/
theorem sectionRange_le_iff_integralPoints_le
    {source₂ : RelativeComponentModelData R K G}
    (ψ : RelativeComponentModelHom source₂ target) :
    (rationalPoints.map φ.neutral.hom).range ≤
        (rationalPoints.map ψ.neutral.hom).range ↔
      source.neutral.integralPoints ≤ source₂.neutral.integralPoints := by
  rw [φ.sectionRange_eq_comap_integralPoints, ψ.sectionRange_eq_comap_integralPoints]
  exact Subgroup.comap_le_comap_of_le_range φ.neutral_integralPoints_le

section AlgClosed

variable [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]

/-- Over an algebraically closed residue field, every rational point of the
actual schematic image lifts through its canonical projection. -/
theorem specialFibreImageProjection_surjective_of_isAlgClosed :
    Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap)) := by
  have : GeometricallyIntegral source.neutral.specialFibre.X.hom :=
    smoothConnectedAffineGeometry.1 _ _ inferInstance inferInstance inferInstance
  have : Surjective (SchematicImage.projection φ.neutralSpecialFibreMap).hom.hom.left :=
    HomImage.surjective_projection φ.neutralSpecialFibreMap
  exact GroupScheme.rationalPoints_surjective
    (SchematicImage.projection φ.neutralSpecialFibreMap)

end AlgClosed

section Henselian

variable [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]

/-- Congruence containment recovers the exact reduction preimage over an
algebraically closed residue field, without a kernel hypothesis on the
special-fibre map. -/
theorem hasParabolicReductionPreimage_of_congruence
    (hker : target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints) :
    φ.HasParabolicReductionPreimage :=
  (φ.hasParabolicReductionPreimage_iff source.neutral_smooth
    φ.specialFibreImageProjection_surjective_of_isAlgClosed).mpr
      (φ.congruenceKernel_le_sectionRange_iff.mpr hker)

/-- The neutral section map identifies the source section group with the full
reduction preimage of its actual special-fibre image. -/
def reductionPreimageMulEquiv
    (hker : target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints) :
    source.neutral.integralSections ≃*
      φ.specialFibreImagePoints.comap target.neutral.reduction :=
  (MonoidHom.ofInjective φ.neutralSectionMap_injective).trans
    (MulEquiv.subgroupCongr (φ.hasParabolicReductionPreimage_of_congruence hker).symm)

/-- The equivalence is the given neutral section map on underlying sections. -/
@[simp] theorem reductionPreimageMulEquiv_apply
    (hker : target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints)
    (x : source.neutral.integralSections) :
    (φ.reductionPreimageMulEquiv hker x : target.neutral.integralSections) =
      rationalPoints.map φ.neutral.hom x :=
  rfl

variable {source₂ : RelativeComponentModelData R K G}
  (ψ : RelativeComponentModelHom source₂ target)

/-- Rational-point order of the two actual special-fibre images is exactly
generic integral-point order, when both sources contain the target congruence
subgroup. -/
theorem specialFibreImagePoints_le_iff_integralPoints_le
    (hφ : target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints)
    (hψ : target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints) :
    φ.specialFibreImagePoints ≤ ψ.specialFibreImagePoints ↔
      source.neutral.integralPoints ≤ source₂.neutral.integralPoints := by
  rw [← Subgroup.comap_le_comap_of_surjective
    (target.neutral.reduction_surjective target.neutral_smooth),
    φ.hasParabolicReductionPreimage_of_congruence hφ,
    ψ.hasParabolicReductionPreimage_of_congruence hψ]
  exact φ.sectionRange_le_iff_integralPoints_le ψ

/-- Containment of the actual schematic-image subgroup functors on every test
scheme is equivalent to containment of the generic integral-point subgroups. -/
theorem specialFibreImage_le_iff_integralPoints_le
    (hφ : target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints)
    (hψ : target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints) :
    SubgroupFunctor.range φ.specialFibreImageInclusion ≤
        SubgroupFunctor.range ψ.specialFibreImageInclusion ↔
      source.neutral.integralPoints ≤ source₂.neutral.integralPoints := by
  have : GeometricallyReduced source.neutral.specialFibre.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
  have : Smooth φ.specialFibreImage.X.hom :=
    HomImage.smooth_image φ.neutralSpecialFibreMap
  have : IsReduced φ.specialFibreImage.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (IsLocalRing.ResidueField R) φ.specialFibreImage.X.left
        φ.specialFibreImage.X.hom
  have hclosed : IsClosedSubgroup ψ.specialFibreImageInclusion :=
    inferInstanceAs (IsClosedImmersion ψ.specialFibreImageInclusion.hom.hom.left)
  exact (SubgroupFunctor.range_le_iff_algClosed_points hclosed).trans
    (φ.specialFibreImagePoints_le_iff_integralPoints_le ψ hφ hψ)

/-- Equality of actual schematic-image subgroup functors is exactly equality
of generic integral-point subgroups, under the same congruence containments. -/
theorem specialFibreImage_eq_iff_integralPoints_eq
    (hφ : target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints)
    (hψ : target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints) :
    SubgroupFunctor.range φ.specialFibreImageInclusion =
        SubgroupFunctor.range ψ.specialFibreImageInclusion ↔
      source.neutral.integralPoints = source₂.neutral.integralPoints := by
  rw [le_antisymm_iff, le_antisymm_iff,
    φ.specialFibreImage_le_iff_integralPoints_le ψ hφ hψ,
    ψ.specialFibreImage_le_iff_integralPoints_le φ hψ hφ]

end Henselian

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom
