import Langlands.AlgebraicGeometry.ProjectiveSpace.BoundedHomogeneousEquations
import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearSectionGenerationOpen
import Langlands.AlgebraicGeometry.Modules.PrincipalGenerationOpenLiftProof
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing
import Langlands.AlgebraicGeometry.LinearSystem.TwistComparison

/-! # A homogeneous form as a section, and its scheme-theoretic vanishing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MvPolynomial
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {m : ℕ}

/-- The degree-`d` twist on polynomial projective space, packaged as an actual line bundle. -/
def twistLineBundle (A : Type u) [CommRing A] (m d : ℕ) : LineBundle (ProjectiveSpace A m) :=
  ⟨projTwistingSheaf (projectiveSpaceGrading A m) d, by
    intro x
    have hx : x ∈ ⨆ j, projectiveSpaceCoordinateOpen A m j := by
      rw [iSup_projectiveSpaceCoordinateOpen]; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    let U := projectiveSpaceCoordinateOpen A m j
    have hdeg : X j ^ d ∈ projectiveSpaceGrading A m d :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X_pow j d)
    let s := projTwistingSheafSection (projectiveSpaceGrading A m) d _ hdeg
    have hU : U ≤ Proj.basicOpen (projectiveSpaceGrading A m) (X j ^ d) := by
      intro y hy
      exact fun h => hy (Ideal.IsPrime.mem_of_pow_mem inferInstance d h)
    have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (sectionHom _ s)) :=
      ProjTwist.trivializesOn_projTwistingSheafSection hdeg hU
    exact ⟨U, hj, ⟨(asIso (f := (Scheme.Modules.restrictFunctor U.ι).map (sectionHom _ s))).symm ≪≫
      Scheme.Modules.restrictUnitIso U.ι⟩⟩⟩

/-- The section `F / 1` of the actual twist corresponding to a homogeneous form. -/
def homogeneousSection {d : ℕ} {F : ProjectiveCoordinateRing A m}
    (hF : F.IsHomogeneous d) : GlobalSections (twistLineBundle A m d).obj :=
  projTwistingSheafSection (projectiveSpaceGrading A m) d F
    ((mem_homogeneousSubmodule _ _).mpr hF)

/-- The chart frame of the twist of degree `d` is the section `Xⱼ^d / 1`. -/
lemma trivializesOn_homogeneousCoordinate (j : Fin (m + 1)) (d : ℕ) :
    TrivializesOn (twistLineBundle A m d).obj
      (homogeneousSection (isHomogeneous_X_pow j d : (X j ^ d : ProjectiveCoordinateRing A m).IsHomogeneous d))
      (projectiveSpaceCoordinateOpen A m j) := by
  apply ProjTwist.trivializesOn_projTwistingSheafSection
  intro y hy
  exact fun h => hy (Ideal.IsPrime.mem_of_pow_mem inferInstance d h)

/-- On the chart `D₊(Xⱼ)`, the coefficient of the section of a form `F` in the frame
`Xⱼ^d / 1` is its dehomogenization `F / Xⱼ^d`. -/
lemma homogeneousSection_restrict {d : ℕ} {F : ProjectiveCoordinateRing A m}
    (hF : F.IsHomogeneous d) (j : Fin (m + 1)) :
    sectionRes (twistLineBundle A m d).obj (homogeneousSection hF)
        (projectiveSpaceCoordinateOpen A m j) =
      homogeneousChartSection j hF • sectionRes (twistLineBundle A m d).obj
        (homogeneousSection (isHomogeneous_X_pow j d))
        (projectiveSpaceCoordinateOpen A m j) := by
  apply Subtype.ext
  funext x
  change Localization.mk F 1 = _
  rw [ProjTwist.sectionsInType_smul_apply]
  change Localization.mk F 1 = Localization.mk F ⟨X j ^ d, _⟩ * Localization.mk (X j ^ d) 1
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [mul_comm]⟩

/-- The generation open of `F / 1` is precisely the homogeneous basic open `D₊(F)`. -/
theorem trivializationOpen_homogeneousSection {d : ℕ} {F : ProjectiveCoordinateRing A m}
    (hF : F.IsHomogeneous d) :
    trivializationOpen (twistLineBundle A m d).obj (homogeneousSection hF) =
      Proj.basicOpen (projectiveSpaceGrading A m) F := by
  refine le_antisymm ?_ ((maximalTrivialization _ _ _ _).mp
    (ProjTwist.trivializesOn_projTwistingSheafSection ((mem_homogeneousSubmodule _ _).mpr hF) le_rfl))
  intro x hx
  obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp hx
  have hcov : x ∈ ⨆ j, projectiveSpaceCoordinateOpen A m j := by
    rw [iSup_projectiveSpaceCoordinateOpen]; trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hcov
  let q := homogeneousSection (isHomogeneous_X_pow j d :
    (X j ^ d : ProjectiveCoordinateRing A m).IsHomogeneous d)
  obtain ⟨c, hc⟩ := ((LineBundleDescent.trivializesOn_iff_bijective _ _ V).mp hV V le_rfl).2
    (sectionRes _ q V)
  rw [LineBundleDescent.sectionHom_app] at hc
  have he : (c.1 ⟨x, hxV⟩).val * Localization.mk F 1 = Localization.mk (X j ^ d) 1 :=
    congrFun (congrArg Subtype.val hc) ⟨x, hxV⟩
  have hu : IsUnit (Localization.mk F 1 : ProjTwist.Localizations (projectiveSpaceGrading A m) x) :=
    isUnit_of_mul_isUnit_right (he ▸ ProjTwist.isUnit_mk_one x
      (fun h => hj (Ideal.IsPrime.mem_of_pow_mem inferInstance d h)))
  rw [Localization.mk_one_eq_algebraMap] at hu
  exact (IsLocalization.AtPrime.isUnit_to_map_iff
    (ProjTwist.Localizations (projectiveSpaceGrading A m) x) _ _).mp hu

/-- A homogeneous form vanishes in the scheme-theoretic kernel precisely when its
section of the twist pulls back to the zero section. -/
theorem homogeneousVanishes_ker_iff_pullbackSection_eq_zero
    {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A m) [QuasiCompact i]
    {d : ℕ} {F : ProjectiveCoordinateRing A m} (hF : F.IsHomogeneous d) :
    HomogeneousVanishes i.ker hF ↔
      pullbackSection i (twistLineBundle A m d).obj (homogeneousSection hF) = 0 := by
  let L := twistLineBundle A m d
  let M := (Scheme.Modules.pullback i).obj L.obj
  let U := projectiveSpaceCoordinateOpen A m
  let V := fun j => i ⁻¹ᵁ U j
  let s := pullbackSection i L.obj (homogeneousSection hF)
  let q := fun j : Fin (m + 1) => homogeneousSection (isHomogeneous_X_pow j d :
    (X j ^ d : ProjectiveCoordinateRing A m).IsHomogeneous d)
  let t := fun j => pullbackSection i L.obj (q j)
  have ht (j) : V j ≤ trivializationOpen M (t j) := by
    rw [show trivializationOpen M (t j) = i ⁻¹ᵁ trivializationOpen L.obj (q j) from
      lineBundlePullbackSectionOpen _ _ i L (q j)]
    exact i.preimage_mono ((maximalTrivialization _ _ _ _).mp (trivializesOn_homogeneousCoordinate j d))
  have hs (j) : sectionRes M s (V j) =
      i.app (U j) (homogeneousChartSection j hF) • sectionRes M (t j) (V j) :=
    LinearSystem.pullbackSection_restrict_smul _ _ _ _ _ _ (homogeneousSection_restrict hF j)
  rw [homogeneousVanishes_ker_iff i hF]
  change (∀ j, i.app (U j) (homogeneousChartSection j hF) = 0) ↔ s = 0
  constructor
  · intro h
    apply TopCat.Sheaf.eq_of_locally_eq' (Langlands.Scheme.Modules.OpenCoverHomGluing.sheafAb M)
      V ⊤ (fun j => homOfLE le_top)
      (i.iSup_preimage_eq_top (iSup_projectiveSpaceCoordinateOpen A m)).ge
    intro j
    change sectionRes M s (V j) = _
    rw [hs, h, zero_smul, map_zero]
  · intro h j
    have hbij := bijective_sectionHom_app_of_le M (t j) (ht j)
    apply hbij.injective
    rw [LineBundleDescent.sectionHom_app, LineBundleDescent.sectionHom_app,
      ← hs, h, zero_smul]
    exact map_zero _

end Langlands.AlgebraicGeometry.ProjectiveSpace
