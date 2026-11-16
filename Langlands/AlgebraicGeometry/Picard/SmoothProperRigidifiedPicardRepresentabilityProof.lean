import Langlands.AlgebraicGeometry.Picard.SmoothProperRigidifiedPicardRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedRepresentationUniversalBundleProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Picard.FieldPicardSheafRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Langlands.AlgebraicGeometry.Picard.FieldPicardSheafRepresentabilityReduction
import Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasProof

/-! # Full rigidified Picard representability for smooth proper pointed schemes: proof

Proper-field fppf Picard-sheaf representability (from the published field
Picard stack atlas and the published reduction), the published canonical
rigidified/fppf comparison and the published universal global-functions theorem
combine with the published representation-to-universal-bundle theorem.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The universal canonical structure-sheaf condition holds on every open of
every test scheme for a smooth proper geometrically connected morphism. -/
theorem universalStructureSheafOfSmoothProper {S X : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f] [GeometricallyConnected f] :
    ∀ (T : Over S) (U : T.left.Opens),
      IsIso (((relativeProjection f).app T).app U) := by
  intro T U
  exact Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions _ _
    (pullback.fst T.hom f) inferInstance inferInstance inferInstance U

/-- A natural representation of a presheaf `F`, together with an actual natural
isomorphism from the rigidified class presheaf to `F`, gives an actual universal
rigidified line bundle, with no restriction on test schemes. -/
theorem universalBundleOfPicardComparison {S X : Scheme.{u}} (f : X ⟶ S)
    (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) (P : Over S)
    (r : F.RepresentableBy P)
    (comparison :
      RigidifiedLineBundle.classPresheaf
        Langlands.SchemeModule.RigidifiedModule.pullbackCoherence f ε section_eq ≅ F) :
    ∃ L : RigidifiedLineBundle.relative f ε section_eq P,
      RigidifiedLineBundle.IsUniversal f ε section_eq L := by
  obtain ⟨L, hL, -⟩ :=
    RigidifiedLineBundle.representationUniversalBundle S X f ε section_eq
      Langlands.SchemeModule.RigidifiedModule.pullbackCoherence P
      (r.ofIso comparison.symm)
  exact ⟨L, hL⟩

/-- The class-sheaf isomorphism obtained from the canonical map
`RigidifiedLineBundle.toPicardSheaf`, when it is an isomorphism. -/
noncomputable def canonicalPicardComparisonIso {S X : Scheme.{u}} (f : X ⟶ S)
    (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)
    [IsIso (RigidifiedLineBundle.toPicardSheaf f ε section_eq)] :
    RigidifiedLineBundle.classPresheaf
      Langlands.SchemeModule.RigidifiedModule.pullbackCoherence f ε section_eq ≅
        RelativePicard.classSheafPresheaf f :=
  asIso (RigidifiedLineBundle.toPicardSheaf f ε section_eq) ≪≫
    RelativePicard.forgetSheafIso f

/-- Its forward map is exactly forgetting rigidification and taking the
ordinary set-valued sheafification image. -/
@[simp]
theorem canonicalPicardComparisonIso_hom {S X : Scheme.{u}} (f : X ⟶ S)
    (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)
    [IsIso (RigidifiedLineBundle.toPicardSheaf f ε section_eq)] :
    (canonicalPicardComparisonIso f ε section_eq).hom =
      RigidifiedLineBundle.toClassPicardSheaf f ε section_eq :=
  RigidifiedLineBundle.toPicardSheaf_forgetSheafIso_hom f ε section_eq

/-- Every smooth proper geometrically connected pointed scheme over a field has
a separated, locally finite type parameter scheme with an actual universal
rigidified line bundle, classifying families over every test scheme. -/
theorem smoothProperRigidifiedPicardRepresentability :
    SmoothProperRigidifiedPicardRepresentabilityStatement.{u} := by
  intro K _ X hs hp hg ε section_eq
  let := hs
  let := hp
  let := hg
  obtain ⟨P, hsep, hlft, ⟨r⟩⟩ :=
    fieldPicardSheafRepresentability_of_stackAtlas fieldPicardStackAtlas K X hp
  let : IsIso (RigidifiedLineBundle.toPicardSheaf X.hom ε section_eq) :=
    rigidifiedFppfComparison _ _ X.hom inferInstance inferInstance ε section_eq
      (universalStructureSheafOfSmoothProper X.hom)
  obtain ⟨L, hL⟩ := universalBundleOfPicardComparison X.hom ε section_eq
    (RelativePicard.classSheafPresheaf X.hom) P r
    (canonicalPicardComparisonIso X.hom ε section_eq)
  exact ⟨P, L, hsep, hlft, hL⟩

end Langlands.AlgebraicGeometry.Picard
