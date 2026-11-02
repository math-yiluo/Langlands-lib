import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateGenerationOpenProof
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof

/-! # Generation opens of sections of `𝒪(1)` given by linear forms, and their pullbacks -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

universe u

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

/-- The global section `f / 1` of `𝒪(1)` on projective space defined by a linear form `f`. -/
def twistOneLinearSection (R : Type u) [CommRing R] (n : ℕ)
    (f : projectiveSpaceGrading R n 1) : Γ(twistOne R n, ⊤) :=
  projTwistingSheafSection (projectiveSpaceGrading R n) 1 f f.2

/-- The twisting sheaf `𝒪(1)` on projective space as a line bundle. -/
def twistOneLineBundle (R : Type u) [CommRing R] (n : ℕ) : LineBundle (ProjectiveSpace R n) :=
  ⟨twistOne R n, (projectiveSpaceTwistOneLocalFrames R n).2⟩

/-- The whole generation open of the section `f / 1` of `𝒪(1)` attached to a linear form `f`
is the basic open `D₊(f)`. -/
theorem trivializationOpen_twistOneLinearSection (R : Type u) [CommRing R] (n : ℕ)
    (f : projectiveSpaceGrading R n 1) :
    trivializationOpen (twistOne R n) (twistOneLinearSection R n f) =
      Proj.basicOpen (projectiveSpaceGrading R n) (f : ProjectiveCoordinateRing R n) := by
  refine le_antisymm ?_ ((maximalTrivialization _ _ _ _).mp
    (ProjTwist.trivializesOn_projTwistingSheafSection f.2 le_rfl))
  intro x hx
  obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
  have hcov : x ∈ ⨆ j : Fin (n + 1), projectiveSpaceCoordinateOpen R n j := by
    rw [iSup_projectiveSpaceCoordinateOpen R n]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  obtain ⟨g, hg⟩ :=
    ((LineBundleDescent.trivializesOn_iff_bijective _ _ V).mp hV V le_rfl).2
      ((twistOne R n).presheaf.map (homOfLE le_top : V ⟶ ⊤).op (twistOneCoordinate R n j))
  rw [LineBundleDescent.sectionHom_app] at hg
  have e : (g.1 ⟨x, hxV⟩).val * Localization.mk (f : ProjectiveCoordinateRing R n) 1 =
      Localization.mk (MvPolynomial.X j) 1 :=
    congrFun (congrArg Subtype.val hg) ⟨x, hxV⟩
  have hu : IsUnit (Localization.mk (f : ProjectiveCoordinateRing R n) 1 :
      ProjTwist.Localizations (projectiveSpaceGrading R n) x) :=
    isUnit_of_mul_isUnit_right (e ▸ ProjTwist.isUnit_mk_one x hj)
  rw [Localization.mk_one_eq_algebraMap] at hu
  exact (IsLocalization.AtPrime.isUnit_to_map_iff
    (ProjTwist.Localizations (projectiveSpaceGrading R n) x) _ _).mp hu

/-- A point lies in the generation open of `f / 1` iff `f` is not in its homogeneous prime. -/
theorem mem_trivializationOpen_twistOneLinearSection_iff (R : Type u) [CommRing R] (n : ℕ)
    (f : projectiveSpaceGrading R n 1) (x : ProjectiveSpace R n) :
    x ∈ trivializationOpen (twistOne R n) (twistOneLinearSection R n f) ↔
      (f : ProjectiveCoordinateRing R n) ∉ x.asHomogeneousIdeal := by
  rw [trivializationOpen_twistOneLinearSection]
  exact Proj.mem_basicOpen _ _ _

end Langlands.AlgebraicGeometry

namespace Langlands.SchemeModule

universe u

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Pull a section of a line bundle back along a morphism and transport it along an
isomorphism of the pulled-back module with a module `N`. -/
def isoPullbackSection {X Y : Scheme.{u}} (g : Y ⟶ X) (L : LineBundle X) {N : Y.Modules}
    (e : (Scheme.Modules.pullback g).obj L.obj ≅ N) (s : GlobalSections L.obj) :
    GlobalSections N :=
  e.hom.app ⊤ (pullbackSection g L.obj s)

/-- The generation open of an isomorphism-transported pullback section is the inverse image
of the original generation open. -/
theorem trivializationOpen_isoPullbackSection {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : LineBundle X) {N : Y.Modules}
    (e : (Scheme.Modules.pullback g).obj L.obj ≅ N) (s : GlobalSections L.obj) :
    trivializationOpen N (isoPullbackSection g L e s) = g ⁻¹ᵁ trivializationOpen L.obj s := by
  unfold isoPullbackSection
  rw [trivializationOpen_mapIso e, lineBundlePullbackSectionOpen]

end Langlands.SchemeModule
