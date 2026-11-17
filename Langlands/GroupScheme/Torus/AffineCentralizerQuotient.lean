import Langlands.GroupScheme.CentralizerAffineOrbit
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.RelativeQuasiAffineHomogeneousQuotient
import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth

/-! # Quasi-affine centralizer quotients over a ring -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace AffineCoordinates

open Corepresented

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  [IsAffine G.X.left] (i : H ⟶ G) (I : Ideal (algebra G))

/-- The coefficient orbit map transported to the original affine group. -/
def centralizerCoefficientOrbit : G.X ⟶ conjugationCoefficientScheme I :=
  (groupSchemeIso G).inv.hom.hom ≫
    conjugationCoefficientOrbit (corepresentation G) I

variable {I}

/-- Coordinate transport preserves the exact centralizer fibers on every
scheme test. -/
theorem centralizerCoefficientOrbit_fibers
    (hI : ∀ (U : Over (Spec R))
      (y : U ⟶ (Corepresented.groupScheme (functor G) (corepresentation G)).X),
      y ∈ (SubgroupFunctor.range (coordinateHom i)).carrier U ↔
        ∀ b ∈ I, ((corepresentation G).homEquiv.symm
          (pointsEquiv (functor G) (corepresentation G) U y)).hom b = 0)
    [Module.Projective R (algebra G ⧸ I)]
    (T : Over (Spec R)) (g h : T ⟶ G.X) :
    g ≫ centralizerCoefficientOrbit (G := G) I =
        h ≫ centralizerCoefficientOrbit (G := G) I ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range i).centralizer.carrier T := by
  rw [SubgroupFunctor.centralizer_range_eq_comap_of_iso i (groupSchemeIso G).symm,
    SubgroupFunctor.mem_comap]
  simpa only [centralizerCoefficientOrbit, coordinateHom, Iso.symm_hom,
    Category.assoc, MonObj.mul_comp, GrpObj.inv_comp] using
    conjugationCoefficientOrbit_fibers hI T
      (g ≫ (groupSchemeIso G).inv.hom.hom)
      (h ≫ (groupSchemeIso G).inv.hom.hom)

end AffineCoordinates

open Corepresented

/-- Projective subgroup coordinates supply an actual affine parameter map
whose fibers are the full centralizer cosets. -/
theorem exists_affine_centralizer_orbit_of_projective
    {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffine G.X.left]
    [Module.Projective R (((algΓ R).obj H.X).unop)]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    ∃ (Y : Over (Spec R)) (r : G.X ⟶ Y), IsAffineHom Y.hom ∧
      ∀ (T : Over (Spec R)) (g h : T ⟶ G.X),
        g ≫ r = h ≫ r ↔
          g⁻¹ * h ∈ (SubgroupFunctor.range i).centralizer.carrier T := by
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
  let eH : H ≅ cutGroupScheme hcut := hrep₁.isoOfIsRepresentedBy hrep₂
  let eA : CommAlgCat.of R (AffineCoordinates.algebra G ⧸ I) ≅
      ((algΓ R).obj H.X).unop :=
    (affineSectionsIso (CommAlgCat.of R (AffineCoordinates.algebra G ⧸ I))).symm ≪≫
      ((algΓ R).mapIso ((Grp.forget _).mapIso eH)).unop
  let : Module.Projective R (AffineCoordinates.algebra G ⧸ I) :=
    Module.Projective.of_equiv (CommAlgCat.algEquivOfIso eA).symm.toLinearEquiv
  refine ⟨conjugationCoefficientScheme I,
    AffineCoordinates.centralizerCoefficientOrbit (G := G) I, ?_,
    AffineCoordinates.centralizerCoefficientOrbit_fibers i hI⟩
  change IsAffineHom ((algSpec R).obj (op (conjugationCoefficientAlgebra I))).hom
  rw [algSpec_obj_hom]
  exact isAffineHom_of_isAffine (X := Spec (CommRingCat.of (conjugationCoefficientAlgebra I))) _

/-- An arbitrary smooth closed representative of the centralizer has a smooth
quasi-affine homogeneous quotient when the subgroup coordinates are projective. -/
theorem exists_quasiAffine_centralizer_quotient_of_projective
    {R : CommRingCat.{u}} {G H Z : GroupScheme (Spec R)}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Module.Projective R (((algΓ R).obj H.X).unop)]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (z : Z ⟶ G)
    (hz : (SubgroupFunctor.range i).centralizer.IsRepresentedBy z)
    (hzc : IsClosedSubgroup z) (hZ : Smooth Z.X.hom) :
    ∃ Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient z,
      Smooth Q.scheme.hom ∧
        ∀ V : (Spec R).affineOpens,
          (Q.scheme.hom ⁻¹ᵁ (V : (Spec R).Opens)).toScheme.IsQuasiAffine := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨Y, r, hY, hker⟩ := exists_affine_centralizer_orbit_of_projective i hi
  let : IsAffineHom Y.hom := hY
  apply RelativeHomogeneousQuotient.exists_quasiAffine_quotient_of_map_kernel z hzc hZ Y r
  intro T g h
  rw [hker, hz.2]

/-- Every representative of a closed diagonalizable centralizer in a smooth
affine group over a ring admits a smooth quasi-affine homogeneous quotient. -/
theorem diagonalizableCentralizer_exists_quasiAffine_quotient_overRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
    {G Z : GroupScheme (Spec R)} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    (hi : IsClosedSubgroup i) (z : Z ⟶ G)
    (hz : (torusCentralizer i).IsRepresentedBy z) :
    ∃ Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient z,
      Smooth Q.scheme.hom ∧
        ∀ V : (Spec R).affineOpens,
          (Q.scheme.hom ⁻¹ᵁ (V : (Spec R).Opens)).toScheme.IsQuasiAffine := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Module.Projective R
      (((algΓ R).obj (Diagonalizable.groupScheme R M).X).unop) :=
    Module.Projective.of_equiv
      (affineSectionsAlgEquiv (Diagonalizable.algebra R M)).symm.toLinearEquiv
  obtain ⟨C, c, hc, hC, hrep⟩ :=
    diagonalizableCentralizer_hasSmoothClosedRepresentative_overRing i
      (inferInstance : Smooth G.X.hom)
  let eZ : Z ≅ C := hz.isoOfIsRepresentedBy hrep
  have hzc : IsClosedSubgroup z := by
    rw [← hz.isoOfIsRepresentedBy_hom_comp hrep]
    exact (IsClosedSubgroup.of_iso eZ).comp hc
  have hZ : Smooth Z.X.hom :=
    smooth_of_over_iso ((Grp.forget _).mapIso eZ) hC
  rw [torusCentralizer_eq_centralizer_range] at hz
  exact exists_quasiAffine_centralizer_quotient_of_projective i hi z hz hzc hZ

/-- Choose the smooth quasi-affine quotient by any representative of the
centralizer of a closed diagonalizable subgroup over a ring. -/
def diagonalizableCentralizerQuotientOverRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
    {G Z : GroupScheme (Spec R)} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    (hi : IsClosedSubgroup i) (z : Z ⟶ G)
    (hz : (torusCentralizer i).IsRepresentedBy z) :
    {Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient z //
      Smooth Q.scheme.hom ∧
        ∀ V : (Spec R).affineOpens,
          (Q.scheme.hom ⁻¹ᵁ (V : (Spec R).Opens)).toScheme.IsQuasiAffine} :=
  ⟨_, (diagonalizableCentralizer_exists_quasiAffine_quotient_overRing i hi z hz).choose_spec⟩

end Langlands.GroupScheme
