import Langlands.GroupScheme.Rational.PositiveRootStabilizerReduction
import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Relative-root-system assembly from four explicit structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The published sign theorem supplies the sign input of the assembly.
The other four structural inputs remain explicit hypotheses. -/
theorem relativeRootSystem_of_remaining_structural_statements
    (hreflection : RelativeRootReflectionExistenceStatement.{u})
    (hpar : ParabolicDynamicStatement.{u})
    (hself : ParabolicSelfNormalizerStatement.{u})
    (hcent : GenericCentralizerStatement.{u}) :
    RelativeRootSystemStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  obtain ⟨D, _⟩ := hreflection k G hG T i hi
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  have hstab := positiveRootStabilizerReduction relativeRootSignInclusions
    hpar hself hcent k G hG T i hi ν hν
  exact D.hasRelativeRootSystem_of_positive_stabilizer hi.isSplitSubtorus.1
    (hi.isSplitSubtorus.1.finite_relativeRoots i) hν hstab

/-- The full relative-root-system assertion follows from intrinsic integral
reflections, dynamic parabolicity, parabolic self-normalization, and generic
centralizers. These four geometric assertions are not proved by this statement. -/
def RelativeRootSystemReductionStatement : Prop :=
  RelativeRootReflectionExistenceStatement.{u} →
  ParabolicDynamicStatement.{u} →
  ParabolicSelfNormalizerStatement.{u} →
  GenericCentralizerStatement.{u} →
  RelativeRootSystemStatement.{u}

/-- The published sign theorem and chamber-generation construction prove the
conditional assembly, retaining each outstanding geometric input. -/
theorem relativeRootSystemReduction : RelativeRootSystemReductionStatement.{u} :=
  relativeRootSystem_of_remaining_structural_statements

end Langlands.GroupScheme
