import Langlands.ClassFieldTheory.Local.ClosureCoefficients
import Langlands.Cohomology.Continuous.CochainComparisonLawsProof

/-! # Finite Galois cohomology comparison and ordinary closure inflation -/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- The forward comparison for a finite field extension is an additive equivalence.
Its inverse comes from the proved discrete-group cochain comparison. -/
def continuousToRelativeEquiv (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n : ℕ) :
    continuousCohomology n (discreteUnitsRepresentation K L) ≃+
      relativeCohomology K L n := by
  letI := Langlands.Continuous.continuousToOrdinary_isIso
    (discreteUnitsRepresentation K L) n
  exact (asIso (Langlands.Continuous.continuousToOrdinary
    (discreteUnitsRepresentation K L) n)).toLinearEquiv.toAddEquiv

@[simp]
theorem continuousToRelativeEquiv_apply (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n : ℕ)
    (x : continuousCohomology n (discreteUnitsRepresentation K L)) :
    continuousToRelativeEquiv K L n x = continuousToRelative K L n x := rfl

variable (K : Type u) [Field K]
variable (E : IntermediateField K (AlgebraicClosure K))
  [FiniteDimensional K E] [Normal K E]

/-- Actual ordinary relative cohomology maps into continuous absolute cohomology,
using the proved inverse finite-group comparison followed by continuous inflation. -/
def closureInflation (n : ℕ) :
    relativeCohomology K E n →+ absoluteCohomology K n :=
  (closureContinuousInflation K E n).hom.toAddMonoidHom.comp
    (continuousToRelativeEquiv K E n).symm.toAddMonoidHom

/-- The ordinary inflation agrees with continuous inflation on every continuous class. -/
theorem closureInflation_continuousToRelative (n : ℕ)
    (x : continuousCohomology n (discreteUnitsRepresentation K E)) :
    closureInflation K E n (continuousToRelative K E n x) =
      closureContinuousInflation K E n x := by
  change closureContinuousInflation K E n
      ((continuousToRelativeEquiv K E n).symm
        (continuousToRelativeEquiv K E n x)) = _
  rw [AddEquiv.symm_apply_apply]


end Langlands.ClassFieldTheory.Local
