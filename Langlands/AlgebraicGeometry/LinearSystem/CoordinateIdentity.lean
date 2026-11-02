import Langlands.AlgebraicGeometry.LinearSystem.TwistComparison
import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts

/-! # The linear system of projective coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual degree-one projective twist, packaged as a line bundle over any ring. -/
def projectiveCoordinateLineBundle (R : Type u) [CommRing R] (n : ℕ) :
    LineBundle (ProjectiveSpace R n) :=
  ⟨twistOne R n, (projectiveSpaceTwistOneLocalFrames R n).2⟩

/-- The projective coordinate sections have no common zero. -/
lemma projectiveCoordinates_generate (R : Type u) [CommRing R] (n : ℕ) :
    ∀ x : ProjectiveSpace R n, ∃ i,
      x ∈ nonvanishingLocus (projectiveCoordinateLineBundle R n).obj
        (twistOneCoordinate R n i) := by
  intro x
  have hx : x ∈ ⨆ i, projectiveSpaceCoordinateOpen R n i := by
    rw [iSup_projectiveSpaceCoordinateOpen]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨i, ?_⟩
  rw [lineBundleResidueOpenComparison]
  exact projectiveSpaceCoordinateGenerationOpen R n i ▸ hi

/-- Along a map into a coordinate chart, the ratio of coordinate sections is
the pullback of the actual projective coordinate ratio. -/
lemma sectionRatio_projectiveCoordinates {R : Type u} [CommRing R] {n : ℕ}
    {T : Scheme.{u}} (g : T ⟶ ProjectiveSpace R n) (i j : Fin (n + 1))
    (hg : ⊤ ≤ g ⁻¹ᵁ projectiveSpaceCoordinateOpen R n i) :
    sectionRatio (projectiveCoordinateLineBundle R n) g
        (twistOneCoordinate R n j) (twistOneCoordinate R n i) =
      g.appLE (projectiveSpaceCoordinateOpen R n i) ⊤ hg
        (projectiveSpaceCoordinateRatio R n i j) := by
  have hgi : ∀ t, g t ∈ trivializationOpen
      (projectiveCoordinateLineBundle R n).obj (twistOneCoordinate R n i) := by
    intro t
    change g t ∈ trivializationOpen (twistOne R n) (twistOneCoordinate R n i)
    rw [projectiveSpaceCoordinateGenerationOpen]
    exact hg (by trivial)
  apply (sectionRatio_eq_iff hgi _ _).mpr
  exact (pullbackSection_smul_of_restrict g (twistOne R n) _ _
    (projectiveSpaceCoordinateOpen R n i) (projectiveSpaceCoordinateRatio R n i j)
    (twistOneCoordinate_restrict_coordinateOpen R n i j) hg).symm

section AffineChart

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- On the affine Proj chart, the localization-to-section map pulls back by
the chart inclusion to the canonical affine section isomorphism. -/
lemma awayι_appLE_awayToSection {t : A} {d : ℕ}
    (ht : t ∈ 𝒜 d) (hd : 0 < d)
    (h : ⊤ ≤ (Proj.awayι 𝒜 t ht hd) ⁻¹ᵁ Proj.basicOpen 𝒜 t) :
    Proj.awayToSection 𝒜 t ≫
      (Proj.awayι 𝒜 t ht hd).appLE (Proj.basicOpen 𝒜 t) ⊤ h =
        (Scheme.ΓSpecIso _).inv := by
  let U := Proj.basicOpen 𝒜 t
  let a := Proj.basicOpenIsoSpec 𝒜 t ht hd
  have hi : ⊤ ≤ U.ι ⁻¹ᵁ U := by simp
  have hι : U.ι.appLE U ⊤ hi = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  have ha : Proj.awayToSection 𝒜 t ≫ U.topIso.inv =
      (Scheme.ΓSpecIso _).inv ≫ a.hom.appTop := by
    rw [show a.hom.appTop = (Proj.basicOpenToSpec 𝒜 t).app ⊤ from rfl,
      Proj.basicOpenToSpec_app_top, Iso.inv_hom_id_assoc]
  change Proj.awayToSection 𝒜 t ≫ (a.inv ≫ U.ι).appLE U ⊤ h = _
  rw [← Scheme.Hom.appLE_comp_appLE a.inv U.ι U ⊤ ⊤ hi (by simp), hι,
    ← Category.assoc, ha]
  have hat : a.inv.appLE ⊤ ⊤ (by simp) = a.inv.appTop := by
    simp [Scheme.Hom.appLE]
  rw [hat, Category.assoc, ← Scheme.Hom.comp_appTop, a.inv_hom_id,
    Scheme.Hom.id_appTop, Category.comp_id]

end AffineChart

section Coordinates

variable (R : Type u) [CommRing R] (n : ℕ)

/-- An actual affine coordinate chart lands in the generation open of its
denominator coordinate section. -/
lemma affineChart_mem_projectiveCoordinate (i : Fin (n + 1)) :
    ∀ t, (ProjectiveSpace.affineOpenCover R n).openCover.f i t ∈
      trivializationOpen (projectiveCoordinateLineBundle R n).obj
        (twistOneCoordinate R n i) := by
  intro t
  change (ProjectiveSpace.affineOpenCover R n).openCover.f i t ∈
    trivializationOpen (twistOne R n) (twistOneCoordinate R n i)
  rw [projectiveSpaceCoordinateGenerationOpen,
    ← ProjectiveSpace.affineOpenCover_opensRange]
  exact ⟨t, rfl⟩

/-- The localization ring map of the projective coordinate linear system on an
actual affine coordinate chart is the canonical affine section isomorphism. -/
lemma awayLift_projectiveCoordinates (i : Fin (n + 1)) :
    awayLift (projectiveSpaceGrading R n)
        (chartRingHom (L := projectiveCoordinateLineBundle R n)
          (projectiveSpaceToSpec R n) (twistOneCoordinate R n)
          ((ProjectiveSpace.affineOpenCover R n).openCover.f i) i)
        (MvPolynomial.X i)
        (isUnit_chartRingHom_X _ _ (affineChart_mem_projectiveCoordinate R n i)) =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (projectiveSpaceGrading R n) (MvPolynomial.X i)))).inv.hom := by
  let g := (ProjectiveSpace.affineOpenCover R n).openCover.f i
  have hg : ⊤ ≤ g ⁻¹ᵁ projectiveSpaceCoordinateOpen R n i := by
    rw [← ProjectiveSpace.affineOpenCover_opensRange R n i]
    simp [g]
  have hc : Scheme.Modules.scalarsFromBase (g ≫ projectiveSpaceToSpec R n) =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (projectiveSpaceGrading R n) (MvPolynomial.X i)))).inv.hom.comp
        (algebraMap R (HomogeneousLocalization.Away
          (projectiveSpaceGrading R n) (MvPolynomial.X i))) := by
    unfold Scheme.Modules.scalarsFromBase
    rw [ProjectiveSpace.affineOpenCover_comp_toSpec,
      ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  ext x
  have hx : x ∈ Algebra.adjoin R (Set.range (_root_.AlgebraicGeometry.ProjSpace.ratio R n i)) := by
    rw [_root_.AlgebraicGeometry.ProjSpace.adjoin_range_ratio]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      change awayLift (projectiveSpaceGrading R n) _ _ _
        (HomogeneousLocalization.Away.mk (projectiveSpaceGrading R n)
          (projectiveSpace_X_mem R n i) 1 (MvPolynomial.X j)
          (by simpa using projectiveSpace_X_mem R n j)) = _
      rw [awayLift_mk_eq_iff,
        chartRingHom_X, chartRingHom_X,
        sectionRatio_self (affineChart_mem_projectiveCoordinate R n i),
        one_pow, mul_one, sectionRatio_projectiveCoordinates g i j hg]
      change (Proj.awayToSection (projectiveSpaceGrading R n) (MvPolynomial.X i) ≫
          g.appLE (projectiveSpaceCoordinateOpen R n i) ⊤ hg) _ = _
      have he : Proj.awayToSection (projectiveSpaceGrading R n) (MvPolynomial.X i) ≫
          g.appLE (projectiveSpaceCoordinateOpen R n i) ⊤ hg =
        (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
          (projectiveSpaceGrading R n) (MvPolynomial.X i)))).inv :=
        awayι_appLE_awayToSection (projectiveSpaceGrading R n)
          (projectiveSpace_X_mem R n i) Nat.one_pos hg
      rw [he]
      rfl
  | algebraMap r =>
      change awayLift _ _ _ _
          (HomogeneousLocalization.fromZeroRingHom _ _
            (projectiveSpaceConstants R n r)) = _
      rw [awayLift_fromZeroRingHom, projectiveSpaceConstants_coe, chartRingHom_C]
      change Scheme.Modules.scalarsFromBase (g ≫ projectiveSpaceToSpec R n) r = _
      rw [hc]
      rfl
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | mul x y _ _ hx hy => simp only [map_mul, hx, hy]

/-- On each actual affine chart, the point map defined by the projective
coordinate sections is exactly the original chart inclusion. -/
lemma pointMap_projectiveCoordinates (i : Fin (n + 1)) :
    pointMap (L := projectiveCoordinateLineBundle R n)
        (projectiveSpaceToSpec R n) (twistOneCoordinate R n)
        ((ProjectiveSpace.affineOpenCover R n).openCover.f i) i
        (affineChart_mem_projectiveCoordinate R n i) =
      (ProjectiveSpace.affineOpenCover R n).openCover.f i := by
  unfold pointMap chartMap
  rw [awayLift_projectiveCoordinates, CommRingCat.ofHom_hom]
  change (Spec (CommRingCat.of (HomogeneousLocalization.Away
    (projectiveSpaceGrading R n) (MvPolynomial.X i)))).toSpecΓ ≫
      Spec.map (Scheme.ΓSpecIso _).inv ≫
        Proj.awayι (projectiveSpaceGrading R n) (MvPolynomial.X i)
          (projectiveSpace_X_mem R n i) Nat.one_pos =
      Proj.awayι (projectiveSpaceGrading R n) (MvPolynomial.X i)
        (projectiveSpace_X_mem R n i) Nat.one_pos
  rw [← Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

/-- The linear system of the actual homogeneous coordinate sections recovers
the identity morphism of projective space. -/
lemma linearSystemMap_projectiveCoordinates :
    linearSystemMap (L := projectiveCoordinateLineBundle R n)
        (projectiveSpaceToSpec R n) (projectiveCoordinates_generate R n) =
      𝟙 (ProjectiveSpace R n) := by
  apply (ProjectiveSpace.affineOpenCover R n).openCover.hom_ext
  intro i
  rw [comp_linearSystemMap _ _ _ i (affineChart_mem_projectiveCoordinate R n i),
    pointMap_projectiveCoordinates, Category.comp_id]

end Coordinates

section RelativeCoordinates

/-- The actual coordinate sections of relative projective space have no common zero. -/
lemma relativeProjectiveCoordinates_generate (S : Scheme.{u}) (n : ℕ) :
    ∀ x : RelativeProjectiveSpace S n, ∃ i,
      x ∈ nonvanishingLocus (RelativeProjectiveSpace.twistOne S n).obj
        (RelativeProjectiveSpace.twistOneCoordinate S n i) :=
  pullbackSections_generate (RelativeProjectiveSpace.toIntegral S n)
    (projectiveCoordinates_generate (ULift.{u} ℤ) n)

/-- The integral map of the relative coordinate sections is the actual
projection to the integral projective-space model. -/
lemma integralLinearSystemMap_relativeProjectiveCoordinates (S : Scheme.{u}) (n : ℕ) :
    integralLinearSystemMap (relativeProjectiveCoordinates_generate S n) =
      RelativeProjectiveSpace.toIntegral S n := by
  have he : integralLinearSystemMap (projectiveCoordinates_generate (ULift.{u} ℤ) n) =
      𝟙 (ProjectiveSpace (ULift.{u} ℤ) n) := by
    unfold integralLinearSystemMap
    rw [show specULiftZIsTerminal.from (ProjectiveSpace (ULift.{u} ℤ) n) =
      projectiveSpaceToSpec (ULift.{u} ℤ) n from specULiftZIsTerminal.hom_ext _ _]
    exact linearSystemMap_projectiveCoordinates (ULift.{u} ℤ) n
  change integralLinearSystemMap (pullbackSections_generate
    (RelativeProjectiveSpace.toIntegral S n)
    (projectiveCoordinates_generate (ULift.{u} ℤ) n)) = _
  rw [integralLinearSystemMap_pullback (RelativeProjectiveSpace.toIntegral S n)
    (projectiveCoordinates_generate (ULift.{u} ℤ) n), he, Category.comp_id]

/-- The linear system of the actual relative coordinate sections recovers the
identity of relative projective space over every base scheme. -/
lemma relativeLinearSystemMap_relativeProjectiveCoordinates (S : Scheme.{u}) (n : ℕ) :
    relativeLinearSystemMap (RelativeProjectiveSpace.toBase S n)
        (relativeProjectiveCoordinates_generate S n) =
      𝟙 (RelativeProjectiveSpace S n) := by
  apply RelativeProjectiveSpace.hom_ext
  · simp
  · simp only [relativeLinearSystemMap_toIntegral, Category.id_comp]
    exact integralLinearSystemMap_relativeProjectiveCoordinates S n

end RelativeCoordinates

end Langlands.AlgebraicGeometry.LinearSystem
