import Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.FieldPicardSheafRepresentabilityReduction
import Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasReduction
import Langlands.AlgebraicGeometry.Picard.FiniteTypeVersalChartReduction
import Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityProof
import Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationReduction
import Langlands.AlgebraicGeometry.Picard.SmoothProperRigidifiedPicardRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedRepresentationUniversalBundleProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Reductions of field rigidified Picard representability

Every theorem here keeps an unproved proposition as an explicit hypothesis.
None proves `FieldRigidifiedPicardRepresentabilityStatement` outright.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The general pointed smooth-proper statement specializes to an abelian variety,
using its actual unit section and discarding only separatedness of the parameter. -/
theorem fieldRigidifiedPicardRepresentability_of_smoothProper
    (representation : SmoothProperRigidifiedPicardRepresentabilityStatement.{u}) :
    FieldRigidifiedPicardRepresentabilityStatement.{u} := by
  intro k _ A
  obtain ⟨P, L, _, hlft, hL⟩ :=
    representation k A.X inferInstance inferInstance inferInstance
      (unitSection A) (unitSection_comp A)
  exact ⟨P, L, hlft, hL⟩

/-- Scheme representability of the actual fppf Picard sheaf of a proper scheme over
a field gives the rigidified universal bundle of every abelian variety. The canonical
rigidified/fppf comparison and the universal structure-sheaf condition are supplied
by published proofs. -/
theorem fieldRigidifiedPicardRepresentability_of_fieldPicardSheaf
    (representation : FieldPicardSheafRepresentabilityStatement.{u}) :
    FieldRigidifiedPicardRepresentabilityStatement.{u} := by
  intro k _ A
  obtain ⟨P, _, hlft, ⟨r⟩⟩ := representation k A.X inferInstance
  have hO : ∀ (T : Over (Spec (CommRingCat.of k))) (U : T.left.Opens),
      IsIso (((relativeProjection A.X.hom).app T).app U) := by
    intro T U
    exact Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions _ _
      (pullback.fst T.hom A.X.hom) inferInstance inferInstance inferInstance U
  let : IsIso
      (RigidifiedLineBundle.toPicardSheaf A.X.hom (unitSection A) (unitSection_comp A)) :=
    rigidifiedFppfComparison _ _ A.X.hom inferInstance inferInstance
      (unitSection A) (unitSection_comp A) hO
  let comparison :=
    asIso (RigidifiedLineBundle.toPicardSheaf A.X.hom
      (unitSection A) (unitSection_comp A)) ≪≫
        RelativePicard.forgetSheafIso A.X.hom
  obtain ⟨L, hL, _⟩ :=
    RigidifiedLineBundle.representationUniversalBundle _ _ A.X.hom
      (unitSection A) (unitSection_comp A)
      Langlands.SchemeModule.RigidifiedModule.pullbackCoherence P
      (r.ofIso comparison.symm)
  exact ⟨P, L, hlft, hL⟩

/-- The rigidified universal bundle of every abelian variety over a field, with the
smooth scheme atlas of the actual Picard stack over fields as the remaining input. -/
theorem fieldRigidifiedPicardRepresentability_of_stackAtlas
    (hA : FieldPicardStackAtlasStatement.{u}) :
    FieldRigidifiedPicardRepresentabilityStatement.{u} :=
  fieldRigidifiedPicardRepresentability_of_fieldPicardSheaf
    (fieldPicardSheafRepresentability_of_stackAtlas hA)

/-- The rigidified universal bundle of every abelian variety over a field, with the
smooth scheme atlas of the actual Picard stack over finite-type `ℤ`-algebras as the
remaining input. -/
theorem fieldRigidifiedPicardRepresentability_of_finiteTypeStackAtlas
    (hA : FiniteTypePicardStackAtlasStatement.{u}) :
    FieldRigidifiedPicardRepresentabilityStatement.{u} :=
  fieldRigidifiedPicardRepresentability_of_stackAtlas
    (fieldPicardStackAtlas_of_finiteType hA)

/-- The rigidified universal bundle of every abelian variety over a field, with
formally versal Picard families over complete local bases and their algebraization
as the remaining inputs. Openness of versality is the published proof
`picardOpennessOfVersality`. -/
theorem fieldRigidifiedPicardRepresentability_of_versalInputs
    (hF : FiniteTypeFormalVersalBundleStatement.{u})
    (hV : VersalAlgebraizationStatement.{u}) :
    FieldRigidifiedPicardRepresentabilityStatement.{u} :=
  fieldRigidifiedPicardRepresentability_of_finiteTypeStackAtlas
    (PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs hF hV
      picardOpennessOfVersality)

/-- The rigidified universal bundle of every abelian variety over a field, with
formally versal Picard families over complete local bases and finite-order etale
approximation over finite-type `ℤ`-algebras as the only remaining inputs. -/
theorem fieldRigidifiedPicardRepresentability_of_formalVersal_of_etaleApproximation
    (hF : FiniteTypeFormalVersalBundleStatement.{u})
    (hE : Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u}) :
    FieldRigidifiedPicardRepresentabilityStatement.{u} :=
  fieldRigidifiedPicardRepresentability_of_versalInputs hF
    (versalAlgebraization_of_etaleApproximation hE)

set_option linter.defProp false in
/-- The implication proved by
`fieldRigidifiedPicardRepresentability_of_fieldPicardSheaf`, as a single term from
scheme representability of the actual fppf Picard sheaf over fields to the
abelian-variety rigidified statement. -/
def fieldRigidifiedPicardRepresentabilityOfFieldPicardSheaf :
    FieldPicardSheafRepresentabilityStatement.{u} →
      FieldRigidifiedPicardRepresentabilityStatement.{u} :=
  fieldRigidifiedPicardRepresentability_of_fieldPicardSheaf

end Langlands.AbelianScheme
