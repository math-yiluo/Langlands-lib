import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.HomImage

/-! # Special-fibre image containment from generic reduction preimages -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {M N : IntegralModel R K G} (φ : M.Hom N (𝟙 G))

local instance specialFibre_affine (P : IntegralModel R K G) :
    IsAffineHom P.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd P.group.X.hom
    (residueBaseMap R))
  exact MorphismProperty.pullback_snd _ _ P.affine

local instance specialFibre_isAffine (P : IntegralModel R K G) :
    IsAffine P.specialFibre.X.left :=
  isAffine_of_isAffineHom P.specialFibre.X.hom

variable {U : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}

/-- If the generic points of every target section reducing into `i` are
source-integral, the rational image of `i` lies in the actual schematic image.
Smoothness is required only of the target model. -/
theorem Hom.specialFibreImagePoints_contains_of_preimage
    (hN : N.IsSmooth) (i : U ⟶ N.specialFibre)
    (hle : ((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap ≤
      M.integralPoints) :
    (rationalPoints.map i).range ≤
      (rationalPoints.map (SchematicImage.inclusion φ.specialFibreMap)).range := by
  intro y hy
  obtain ⟨x, hx⟩ := N.reduction_surjective hN y
  have hxpre : N.integralPointMap x ∈
      ((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap :=
    ⟨x, by change N.reduction x ∈ (rationalPoints.map i).range; rwa [hx], rfl⟩
  obtain ⟨z, hz⟩ := hle hxpre
  have hzx : rationalPoints.map φ.hom z = x := by
    apply N.integralPointMap_injective
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      (φ.integralPointMap_naturality z).trans hz
  refine ⟨rationalPoints.map (SchematicImage.projection φ.specialFibreMap)
    (M.reduction z), ?_⟩
  change (M.reduction z ≫ (SchematicImage.projection φ.specialFibreMap).hom.hom) ≫
    (SchematicImage.inclusion φ.specialFibreMap).hom.hom = y
  rw [Category.assoc, ← Grp.comp_hom_hom, SchematicImage.projection_inclusion]
  change rationalPoints.map φ.specialFibreMap (M.reduction z) = y
  rw [← φ.reduction_naturality, hzx, hx]

variable [IsAlgClosed (IsLocalRing.ResidueField R)]
  [IsReduced U.X.left] [LocallyOfFiniteType U.X.hom]

/-- Over algebraically closed residue, reduced finite-type sources turn the
same generic-point containment into containment on every test scheme. -/
theorem Hom.specialFibreImage_contains_of_preimage
    (hN : N.IsSmooth) (i : U ⟶ N.specialFibre)
    (hle : ((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap ≤
      M.integralPoints) :
    SubgroupFunctor.range i ≤
      SubgroupFunctor.range (SchematicImage.inclusion φ.specialFibreMap) := by
  exact SubgroupFunctor.range_le_of_algClosed_points
    (HomImage.isClosedSubgroup_inclusion φ.specialFibreMap)
    (φ.specialFibreImagePoints_contains_of_preimage hN i hle)

/-- The actual morphism into the schematic-image group supplied by generic
containment of the target reduction preimage. -/
def Hom.specialFibreImageFactorOfPreimage
    (hN : N.IsSmooth) (i : U ⟶ N.specialFibre)
    (hle : ((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap ≤
      M.integralPoints) :
    U ⟶ SchematicImage.image φ.specialFibreMap :=
  SubgroupFunctor.factorOfAlgClosedPoints
    (HomImage.isClosedSubgroup_inclusion φ.specialFibreMap)
    (φ.specialFibreImagePoints_contains_of_preimage hN i hle)

/-- The constructed factor composes with the actual image inclusion to `i`. -/
@[reassoc]
theorem Hom.specialFibreImageFactorOfPreimage_comp
    (hN : N.IsSmooth) (i : U ⟶ N.specialFibre)
    (hle : ((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap ≤
      M.integralPoints) :
    φ.specialFibreImageFactorOfPreimage hN i hle ≫
        SchematicImage.inclusion φ.specialFibreMap = i :=
  SubgroupFunctor.factorOfAlgClosedPoints_comp _ _

end Langlands.GroupScheme.IntegralModel
