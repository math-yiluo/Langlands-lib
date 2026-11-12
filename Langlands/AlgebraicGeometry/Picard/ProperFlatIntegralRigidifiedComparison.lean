import Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
import Langlands.AlgebraicGeometry.GeometricallyIntegralConnected
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Rigidified classes and the fppf Picard sheaf for proper flat integral families -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

namespace ProperFlatIntegralRigidifiedComparison

/-- Every base change has the canonical structure-sheaf isomorphism on every open,
without any finiteness condition on the test scheme. -/
lemma relativeProjection_app_isIso {S X : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [GeometricallyIntegral f]
    (T : Over S) (U : T.left.Opens) :
    IsIso (((relativeProjection f).app T).app U) := by
  let : GeometricallyConnected f :=
    Langlands.AbelianScheme.TranslationOfSmoothFamily.geometricallyConnected_of_geometricallyIntegral f
  change IsIso ((CategoryTheory.Limits.pullback.fst T.hom f).app U)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
      (CategoryTheory.Limits.pullback.fst T.hom f) U)

end ProperFlatIntegralRigidifiedComparison

namespace RigidifiedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S)
  [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [GeometricallyIntegral f]
  (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

/-- The specified canonical map from rigidified classes to the actual set-valued
fppf Picard sheaf is an isomorphism for every test object. -/
lemma toClassPicardSheaf_isIso_of_properFlatIntegral :
    IsIso (toClassPicardSheaf f ε section_eq) := by
  have := rigidifiedFppfComparison S X f inferInstance inferInstance ε section_eq
    (ProperFlatIntegralRigidifiedComparison.relativeProjection_app_isIso f)
  rw [← toPicardSheaf_forgetSheafIso_hom]
  infer_instance

/-- The natural identification with the actual fppf Picard class sheaf, on the
whole slice category. Its forward map forgets the rigidification and sheafifies. -/
def properFlatIntegralClassIso :
    classPresheaf Langlands.SchemeModule.RigidifiedModule.pullbackCoherence f ε section_eq ≅
      RelativePicard.classSheafPresheaf f :=
  haveI := toClassPicardSheaf_isIso_of_properFlatIntegral f ε section_eq
  asIso (toClassPicardSheaf f ε section_eq)

@[simp]
lemma properFlatIntegralClassIso_hom :
    (properFlatIntegralClassIso f ε section_eq).hom = toClassPicardSheaf f ε section_eq := rfl

end RigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
