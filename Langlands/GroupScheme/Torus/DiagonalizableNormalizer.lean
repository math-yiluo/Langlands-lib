import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Torus.Diagonalizable

/-! # Closed normalizers with projective coordinates -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open Corepresented

/-- A projective coordinate module suffices for closed normalizer
representability over an arbitrary ring. -/
theorem normalizer_hasClosedRepresentative_of_projective
    {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffine G.X.left]
    [Module.Projective R (((algΓ R).obj H.X).unop)]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    (SubgroupFunctor.range i).normalizer.HasClosedRepresentative := by
  let : IsClosedImmersion i.hom.hom.left := hi
  obtain ⟨I, hI⟩ := exists_ideal_range (AffineCoordinates.coordinateHom i)
  let hcut := isCutOutBy_range hI
  have hrange : SubgroupFunctor.range (AffineCoordinates.coordinateHom i) =
      SubgroupFunctor.range (cutHom hcut) := by
    rw [range_cutHom]
    refine SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_
    exact mem_range_iff_mem_affineSubgroups hI x
  have hrep₁ : (SubgroupFunctor.range (AffineCoordinates.coordinateHom i)).IsRepresentedBy
      (AffineCoordinates.coordinateHom i) := ⟨Over.mono_of_mono_left _, rfl⟩
  have hrep₂ : (SubgroupFunctor.range (AffineCoordinates.coordinateHom i)).IsRepresentedBy
      (cutHom hcut) := ⟨inferInstance, hrange.symm⟩
  let eH : H ≅ cutGroupScheme hcut :=
    hrep₁.isoOfIsRepresentedBy hrep₂
  let eA : CommAlgCat.of R (AffineCoordinates.algebra G ⧸ I) ≅
      ((algΓ R).obj H.X).unop :=
    (affineSectionsIso (CommAlgCat.of R (AffineCoordinates.algebra G ⧸ I))).symm ≪≫
      ((algΓ R).mapIso ((Grp.forget _).mapIso eH)).unop
  let : Module.Projective R (AffineCoordinates.algebra G ⧸ I) :=
    Module.Projective.of_equiv (CommAlgCat.algEquivOfIso eA).symm.toLinearEquiv
  exact ⟨_, _, AffineCoordinates.isClosedSubgroup_normalizer_range hI,
    AffineCoordinates.isRepresentedBy_normalizer_range hI⟩

/-- In particular a closed diagonalizable subgroup has a closed normalizer,
including diagonalizable groups that are not smooth. -/
theorem diagonalizableNormalizer_hasClosedRepresentative_overRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
    {G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    (hi : IsClosedSubgroup i) :
    (torusNormalizer i).HasClosedRepresentative := by
  let : Module.Projective R
      (((algΓ R).obj (Diagonalizable.groupScheme R M).X).unop) :=
    Module.Projective.of_equiv
      (affineSectionsAlgEquiv (Diagonalizable.algebra R M)).symm.toLinearEquiv
  exact normalizer_hasClosedRepresentative_of_projective i hi

namespace Diagonalizable

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (i : (groupScheme R M).toGrp ⟶ G) (hi : IsClosedSubgroup i)

/-- A chosen actual closed normalizer of a diagonalizable subgroup. -/
def normalizerGroupScheme : GroupScheme (Spec R) :=
  (diagonalizableNormalizer_hasClosedRepresentative_overRing i hi).choose

/-- The chosen normalizer's inclusion into the original ambient group. -/
def normalizerHom : normalizerGroupScheme i hi ⟶ G :=
  (diagonalizableNormalizer_hasClosedRepresentative_overRing i hi).choose_spec.choose

/-- The chosen inclusion is closed and represents the normalizer on every test. -/
theorem normalizerHom_spec :
    IsClosedSubgroup (normalizerHom i hi) ∧
      (torusNormalizer i).IsRepresentedBy (normalizerHom i hi) :=
  (diagonalizableNormalizer_hasClosedRepresentative_overRing i hi).choose_spec.choose_spec

end Diagonalizable

end Langlands.GroupScheme
