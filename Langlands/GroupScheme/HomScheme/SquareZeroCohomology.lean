import Langlands.GroupScheme.HomScheme.KernelCorrection
import Langlands.GroupScheme.HomScheme.SquareZeroRelativeReduction

/-! # Actual square-zero homomorphism lifting from reduced cohomology -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HomScheme

/-- The absolute deformation assertion follows from smooth scheme lifting,
the actual regular defect correction and actual kernel conjugacy. -/
theorem absoluteSquareZeroCohomologyLift : AbsoluteSquareZeroCohomologyLiftStatement.{u} := by
  intro R I _ H G _ _ _ hH
  constructor
  · intro f₀
    obtain ⟨s, hs⟩ := exists_schemeLift I H G f₀
    exact exists_homLift_of_schemeLift H G I f₀ s hs hH
  · intro f f' hf
    exact exists_kernelConjugator_of_cohomology H G I f f' hf hH

/-- Reduced-source low-degree vanishing gives the exact relative square-zero
homomorphism lifting and prescribed-conjugator lifting property. -/
theorem squareZeroHomomorphismCohomology : SquareZeroHomomorphismCohomologyStatement.{u} :=
  squareZeroCohomology_of_absolute absoluteSquareZeroCohomologyLift

end Langlands.GroupScheme.HomScheme
