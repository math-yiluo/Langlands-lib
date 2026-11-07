import Langlands.LocalFactor.CommonClosureFiniteQuotient
import Langlands.LocalFactor.CommonClosureInductionTwist
import Langlands.LocalFactor.CommonClosureIrreducibleReduction
import Langlands.VirtualRepresentation.Weil.DegreeZeroReduction

/-!
# Degree-zero generation for actual common-closure Weil groups

The continuous exact Grothendieck group in virtual dimension zero is generated
over the integers by the actual inductions of differences of continuous
character lines from nested finite intermediate fields.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor

open CommonClosure VirtualRepresentation

/-- Degree-zero character-induction generation for every finite p-adic field
and its actual common-closure Weil subgroups. -/
theorem commonClosureDegreeZeroGeneration :
    CommonClosureDegreeZeroGenerationStatement.{uF, uV} := by
  intro p hp F E
  apply le_antisymm (span_characterDifferenceInductionGenerators_le F E)
  apply Weil.degreeZero_le_of_finiteImage_twists (weilSubgroup F E)
    (Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E))
  · intro χ x hx
    exact continuousTwist_mem_span F E χ hx
  · intro χ
    exact characterClass_sub_mem_span F E χ 1
  · intro A hc hf
    simpa only [Weil.reducedClass_apply, ExactGrothendieckGroup.degree_ofRepresentation]
      using finiteImage_sub_mem_span' F E A hc hf
  · intro A hc hi
    exact irreducible_finiteImage_twist F E A hc hi

end Langlands.LocalFactor
