import Langlands.AlgebraicGeometry.ProjectiveSpace.HomogeneousSectionGeometry
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.BoundedHomogeneousEquations

/-! # Affine base change of the native projective degree-one twist -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite MvPolynomial
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (m : ℕ)

private lemma coordinateRatio_eq_homogeneousChartSection (i j : Fin (m + 1)) :
    projectiveSpaceCoordinateRatio A m i j = homogeneousChartSection i
      (isHomogeneous_X A j : (X j : ProjectiveCoordinateRing A m).IsHomogeneous 1) := by
  let 𝒜 := projectiveSpaceGrading A m
  change (Proj.awayToSection 𝒜 (X i)).hom (HomogeneousLocalization.Away.mk 𝒜
    (projectiveSpace_X_mem A m i) 1 (X j) (by rw [one_smul]; exact projectiveSpace_X_mem A m j)) = _
  unfold homogeneousChartSection
  rfl

/-- On corresponding coordinate opens, coefficient extension carries each coordinate
ratio into the same ratio over the new ring. -/
lemma app_coordinateRatio_baseChangeMap (i j : Fin (m + 1))
    (hU : projectiveSpaceCoordinateOpen B m i =
      baseChangeMap A B m ⁻¹ᵁ projectiveSpaceCoordinateOpen A m i) :
    (baseChangeMap A B m).appLE _ _ hU.le (projectiveSpaceCoordinateRatio A m i j) =
      projectiveSpaceCoordinateRatio B m i j := by
  let hF : (X j : ProjectiveCoordinateRing A m).IsHomogeneous 1 := isHomogeneous_X A j
  have ha := ProjSpace.restrictFun_app_app_awayToSection_eq_app_awayToSection_map
    (𝟙 (ProjectiveSpace A m)) B (𝟙 (ProjectiveSpace B m)) (baseChangeMap A B m)
    (by simp [baseChangeMap]) 1 (X j) hF i hU.le
  rw [coordinateRatio_eq_homogeneousChartSection, coordinateRatio_eq_homogeneousChartSection]
  change (baseChangeMap A B m).appLE _ _ hU.le (homogeneousChartSection i hF) = _
  have hb : (baseChangeMap A B m).appLE _ _ hU.le (homogeneousChartSection i hF) =
      homogeneousChartSection i (hF.map (algebraMap A B)) := ha
  rw [hb]
  congr 1
  exact MvPolynomial.map_X _ _

/-- The pullback of the native twist along scalar extension has a comparison to the native
new twist carrying every pulled-back coordinate section to its new coordinate section. -/
theorem exists_twistOneBaseChangeIso :
    ∃ e : (Scheme.Modules.pullback (baseChangeMap A B m)).obj (twistOne A m) ≅ twistOne B m,
      ∀ j, e.hom.app ⊤ (pullbackSection (baseChangeMap A B m) (twistOne A m)
        (twistOneCoordinate A m j)) = twistOneCoordinate B m j := by
  let f := baseChangeMap A B m
  let U := projectiveSpaceCoordinateOpen A m
  let V := projectiveSpaceCoordinateOpen B m
  let L := twistOneLineBundle A m
  let M := twistOne B m
  let N := (Scheme.Modules.pullback f).obj L.obj
  let s := twistOneCoordinate B m
  let t := fun j => pullbackSection f L.obj (twistOneCoordinate A m j)
  have hV (i : Fin (m + 1)) : V i = f ⁻¹ᵁ U i :=
    (ProjSpace.map_preimage_basicOpen_X A B m i).symm
  have hs (i) : trivializationOpen M (s i) = V i :=
    trivializationOpen_twistOneLinearSection B m ⟨X i, projectiveSpace_X_mem B m i⟩
  have ht (i) : trivializationOpen N (t i) = V i := by
    change trivializationOpen N (pullbackSection f L.obj (twistOneCoordinate A m i)) = V i
    rw [lineBundlePullbackSectionOpen _ _ f L _, hV]
    rw [show trivializationOpen L.obj (twistOneCoordinate A m i) = U i from
      trivializationOpen_twistOneLinearSection A m ⟨X i, projectiveSpace_X_mem A m i⟩]
  have hcov : (⨆ i, trivializationOpen M (s i)) = ⊤ := by
    simp only [hs]
    exact iSup_projectiveSpaceCoordinateOpen B m
  change ∃ e : N ≅ M, ∀ j, e.hom.app ⊤ (t j) = s j
  apply LinearSystem.exists_iso_of_matching_sections s t hcov
  · intro i; rw [hs, ht]
  · intro i j W hW c hc
    rw [hs] at hW
    let a := projectiveSpaceCoordinateRatio B m i j
    let b := projectiveSpaceCoordinateRatio A m i j
    have ha : sectionRes M (s j) (V i) = a • sectionRes M (s i) (V i) :=
      twistOneCoordinate_restrict_coordinateOpen B m i j
    have hb : sectionRes N (t j) (f ⁻¹ᵁ U i) =
        f.app (U i) b • sectionRes N (t i) (f ⁻¹ᵁ U i) :=
      LinearSystem.pullbackSection_restrict_smul f L.obj _ _ (U i) b
        (twistOneCoordinate_restrict_coordinateOpen A m i j)
    have hr : (ProjectiveSpace B m).presheaf.map (homOfLE hW).op a = c := by
      have h := congrArg (M.presheaf.map (homOfLE hW).op) ha
      rw [Scheme.Modules.map_smul, sectionRes_res, sectionRes_res] at h
      apply ((LineBundleDescent.trivializesOn_iff_bijective _ _ (V i)).mp
        ((projectiveSpaceTwistOneLocalFrames B m).1 i) W hW).injective
      rw [LineBundleDescent.sectionHom_app, LineBundleDescent.sectionHom_app]
      exact h.symm.trans hc
    have h := congrArg (N.presheaf.map (homOfLE (hW.trans (hV i).le)).op) hb
    rw [Scheme.Modules.map_smul, sectionRes_res, sectionRes_res] at h
    rw [← hr]
    have hmap : (ProjectiveSpace B m).presheaf.map (homOfLE (hW.trans (hV i).le)).op
          (f.app (U i) b) = (ProjectiveSpace B m).presheaf.map (homOfLE hW).op a := by
      dsimp only [a, b, f, U, V]
      rw [← app_coordinateRatio_baseChangeMap A B m i j (hV i)]
      simp only [Scheme.Hom.appLE, ← CommRingCat.comp_apply, Category.assoc, ← Functor.map_comp]
      rfl
    rw [hmap] at h
    exact h

/-- The degree-one twist comparison for scalar extension. -/
def twistOneBaseChangeIso :
    (Scheme.Modules.pullback (baseChangeMap A B m)).obj (twistOne A m) ≅ twistOne B m :=
  (exists_twistOneBaseChangeIso A B m).choose

end Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

attribute [local instance] ULiftInt.algebra

/-- Over a ring spectrum the relative twist pulls back to the actual polynomial twist. -/
def polynomialIsoSpec_twistOneIso (B : Type u) [CommRing B] (m : ℕ) :
    (Scheme.Modules.pullback (polynomialIsoSpec B m).hom).obj
      (twistOne (Spec (CommRingCat.of B)) m).obj ≅ Langlands.AlgebraicGeometry.twistOne B m :=
  (Scheme.Modules.pullbackComp (polynomialIsoSpec B m).hom (toIntegral _ m)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (polynomialIsoSpec_hom_toIntegral B m)).app _ ≪≫
    ProjectiveSpace.twistOneBaseChangeIso (ULift.{u} ℤ) B m

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
