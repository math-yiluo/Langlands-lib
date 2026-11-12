import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeExistenceStatement
import Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricOpenLocusBridgeProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyGeometricPointComparison
import Langlands.AbelianScheme.MumfordTrivialLocus

/-! # Constructing the Picard-zero restriction of an ambient rigidified family -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S) {P : Over S}

/-- The published Mumford criterion supplies the exact open locus on all test schemes. -/
lemma exists_geometricPicardZeroOpenLocus (L : RigidifiedFamily A P) :
    ∃ U : P.left.Opens, IsPicardZeroOpenLocus A L U := by
  obtain ⟨U, hU⟩ := exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion
    (fun G M ↦ ⟨mumfordTrivialLocus G M, fun K _ _ t ↦
      isTranslationInvariant_fibreLineBundle_iff G M K t⟩) A P L
  exact ⟨U, isPicardZeroOpenLocus_of_geometricPoints picardZeroGeometricDetection A L U hU⟩

/-- A chosen open subset detecting the geometric Picard-zero property of actual pullbacks. -/
def geometricPicardZeroOpenLocus (L : RigidifiedFamily A P) : P.left.Opens :=
  (exists_geometricPicardZeroOpenLocus A L).choose

lemma geometricPicardZeroOpenLocus_spec (L : RigidifiedFamily A P) :
    IsPicardZeroOpenLocus A L (geometricPicardZeroOpenLocus A L) :=
  (exists_geometricPicardZeroOpenLocus A L).choose_spec

/-- The actual open parameter scheme obtained from a supplied rigidified family. -/
def geometricPicardZeroParameter (L : RigidifiedFamily A P) : Over S :=
  openLocusParameter P (geometricPicardZeroOpenLocus A L)

/-- The actual rigidified pullback of the supplied family to its Picard-zero parameter. -/
def geometricPicardZeroFamily (L : RigidifiedFamily A P) :
    RigidifiedFamily A (geometricPicardZeroParameter A L) :=
  restrictedRigidifiedFamily A L (geometricPicardZeroOpenLocus A L)

/-- Full ambient universality makes the constructed restriction universal for Picard zero. -/
lemma geometricPicardZeroFamily_universal (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) L) :
    IsUniversalPicardZero A (geometricPicardZeroFamily A L) :=
  restrictedRigidifiedFamily_universal A L (geometricPicardZeroOpenLocus A L) hL
    (geometricPicardZeroOpenLocus_spec A L)

/-- An actual ambient universal rigidified family suffices for dual-scheme existence. -/
lemma hasDualScheme_of_rigidifiedUniversal (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) L) :
    HasDualScheme A :=
  ⟨geometricPicardZeroParameter A L, geometricPicardZeroFamily A L,
    geometricPicardZeroFamily_universal A L hL⟩

/-- Field dual existence reduces to the published full rigidified representability target. -/
theorem fieldDualSchemeExistence_of_rigidifiedRepresentability
    (representability : FieldRigidifiedPicardRepresentabilityStatement.{u}) :
    FieldDualSchemeExistenceStatement.{u} := by
  intro k _ A
  obtain ⟨P, L, _, hL⟩ := representability k A
  exact hasDualScheme_of_rigidifiedUniversal A L hL

end Langlands.AbelianScheme
