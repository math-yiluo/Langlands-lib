import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeDualSchemeGeometryStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalOfPicardZeroUniversal
import Langlands.AlgebraicGeometry.Picard.FiniteTypePicardZeroOpenLocusProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedRepresentationUniversalBundleProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonProof
import Langlands.AlgebraicGeometry.Picard.FiniteTypeDualSchemeGeometryProof

/-! # Finite-type smooth-family representers from a Picard scheme and dual geometry -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Every actual projection `T ×_S A → T` is an isomorphism on sections over every open
of `T`. -/
private lemma relativeProjection_app_isIso_of_abelian (T : Over S) (U : T.left.Opens) :
    IsIso (((relativeProjection A.X.hom).app T).app U) :=
  smoothProperConnectedGlobalFunctions _ _ (pullback.fst T.hom A.X.hom)
    inferInstance inferInstance inferInstance U

/-- Forgetting the unit-section rigidification identifies the actual rigidified class
presheaf of an abelian scheme with the actual fppf Picard class sheaf. -/
lemma toClassPicardSheaf_isIso :
    IsIso (RigidifiedLineBundle.toClassPicardSheaf A.X.hom (unitSection A)
      (unitSection_comp A)) := by
  have := rigidifiedFppfComparison S A.X.left A.X.hom inferInstance inferInstance
    (unitSection A) (unitSection_comp A) (relativeProjection_app_isIso_of_abelian A)
  rw [← RigidifiedLineBundle.toPicardSheaf_forgetSheafIso_hom]
  infer_instance

/-- A scheme representing the actual fppf Picard class sheaf carries an actual universal
rigidified family. -/
theorem exists_isUniversal_of_classSheafPresheaf_representableBy {P : Over S}
    (r : (RelativePicard.classSheafPresheaf A.X.hom).RepresentableBy P) :
    ∃ L : RigidifiedFamily A P,
      RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L := by
  have := toClassPicardSheaf_isIso A
  obtain ⟨L, hL, -⟩ := RigidifiedLineBundle.representationUniversalBundle S A.X.left A.X.hom
    (unitSection A) (unitSection_comp A)
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence P
    (r.ofIso (asIso (RigidifiedLineBundle.toClassPicardSheaf A.X.hom (unitSection A)
      (unitSection_comp A))).symm)
  exact ⟨L, hL⟩

/-- Over a finite-type `ℤ`-algebra, scheme representability of the Picard class sheaf
gives an actual universal geometric Picard-zero family. -/
theorem hasDualScheme_of_finiteTypeAbelianPicardSheafScheme
    (picard : FiniteTypeAbelianPicardSheafSchemeStatement.{u})
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : AbelianScheme (Spec (CommRingCat.of R))) : HasDualScheme A := by
  obtain ⟨P, ⟨r⟩⟩ := picard R A
  obtain ⟨L, hL⟩ := exists_isUniversal_of_classSheafPresheaf_representableBy A r
  obtain ⟨U, hU⟩ := finiteTypePicardZeroOpenLocus R A P L
  exact hasDualScheme_of_isPicardZeroOpenLocus A L U hL hU

/-- The finite-type smooth-family representer follows from scheme representability of the
Picard sheaf and the geometry of the chosen dual, using the published smooth-family
comparison. -/
theorem finiteTypeSmoothFamilyAbelianRepresentability_of_prerequisites
    (picard : FiniteTypeAbelianPicardSheafSchemeStatement.{u})
    (geometry : FiniteTypeDualSchemeGeometryStatement.{u}) :
    FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u} := by
  intro R _ _ A
  have hA := hasDualScheme_of_finiteTypeAbelianPicardSheafScheme picard R A
  exact exists_isUniversalSmoothFamilyOnQuasiSeparatedTests_of_hasDualScheme A
    smoothFamilyPicardZeroComparison hA (geometry R A hA)

/-- The finite-type smooth-family representer follows from scheme representability of the
Picard sheaf alone, using the published geometry of the chosen dual. -/
theorem finiteTypeSmoothFamilyAbelianRepresentability_of_picardSheafScheme
    (picard : FiniteTypeAbelianPicardSheafSchemeStatement.{u}) :
    FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u} :=
  finiteTypeSmoothFamilyAbelianRepresentability_of_prerequisites picard
    finiteTypeDualSchemeGeometry.{u}

end Langlands.AbelianScheme
