import Langlands.AlgebraicGeometry.LinearSystem.TwistComparison
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Picard.ProperAmpleTrivialFiniteProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # A generated linear system of an ample line bundle on a proper scheme is finite -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The map from a residue-field spectrum to the scheme is affine, whether or not
its image is closed. -/
lemma isAffineHom_fromSpecResidueField (y : Y) : IsAffineHom (Y.fromSpecResidueField y) := by
  constructor
  intro U _
  by_cases h : y ∈ U
  · rw [show Y.fromSpecResidueField y ⁻¹ᵁ U = ⊤ from top_unique fun x _ ↦ by
      simpa only [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply] using h]
    exact isAffineOpen_top _
  · rw [show Y.fromSpecResidueField y ⁻¹ᵁ U = ⊥ from bot_unique fun x hx ↦ by
      exact (h (by simpa only [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply] using hx)).elim]
    exact isAffineOpen_bot _

/-- The restriction of `f*L` to a scheme-theoretic fibre of `f` is trivial. -/
def fibrePullbackLineBundleTrivialization (f : X ⟶ Y) (L : LineBundle Y) (y : Y) :
    ((LineBundle.pullback (f.fiberι y)).obj ((LineBundle.pullback f).obj L)).obj ≅
      structureSheaf (f.fiber y) :=
  (Scheme.Modules.pullbackComp (f.fiberι y) f).app L.obj ≪≫
    (Scheme.Modules.pullbackCongr (f.fiber_fac y)).app L.obj ≪≫
    ((Scheme.Modules.pullbackComp (f.fiberToSpecResidueField y)
      (Y.fromSpecResidueField y)).app L.obj).symm ≪≫
    (Scheme.Modules.pullback (f.fiberToSpecResidueField y)).mapIso
      (fieldLineBundleTriviality (Y.residueField y)
        ((LineBundle.pullback (Y.fromSpecResidueField y)).obj L)).some ≪≫
    pullbackUnitIso (f.fiberToSpecResidueField y)

/-- A proper morphism with an ample pullback of a target line bundle is finite. -/
lemma isFinite_of_isAmple_pullback (f : X ⟶ Y) [IsProper f] (L : LineBundle Y)
    (hL : ((LineBundle.pullback f).obj L).IsAmple) : IsFinite f := by
  refine (IsFinite.iff_isProper_and_locallyQuasiFinite f).mpr ⟨inferInstance, ?_⟩
  apply locallyQuasiFinite_iff_isFinite_fiber.mpr
  intro y
  have : IsAffineHom (Y.fromSpecResidueField y) := isAffineHom_fromSpecResidueField y
  have : IsAffineHom (f.fiberι y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).flip inferInstance
  have hp : IsProper (f.fiberToSpecResidueField y) := inferInstanceAs (IsProper (pullback.snd f _))
  exact properAmpleTrivialFinite (Y.residueField y) _ (f.fiberToSpecResidueField y)
    _ hp (hL.pullback_of_isAffineHom (f.fiberι y)) ⟨fibrePullbackLineBundleTrivialization f L y⟩

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

open Langlands.SchemeModule Picard

/-- A finite collection of globally generating sections of an ample line bundle on a
proper scheme over a field defines a finite morphism to projective space. -/
lemma isFinite_linearSystemMap_of_isAmple {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] {L : LineBundle X}
    (hL : L.IsAmple) {n : ℕ} {s : Fin (n + 1) → GlobalSections L.obj}
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    IsFinite (linearSystemMap p hs) := by
  have : IsProper (linearSystemMap p hs ≫ projectiveSpaceToSpec K n) := by
    rwa [linearSystemMap_toSpec]
  have : IsProper (linearSystemMap p hs) := IsProper.of_comp _ (projectiveSpaceToSpec K n)
  let M : LineBundle (ProjectiveSpace K n) := ⟨twistOne K n, (projectiveSpaceTwistOneLocalFrames K n).2⟩
  apply isFinite_of_isAmple_pullback (linearSystemMap p hs) M
  exact ampleIso X L _ ⟨(linearSystemTwistIso p s hs).symm⟩ hL

end Langlands.AlgebraicGeometry.LinearSystem
