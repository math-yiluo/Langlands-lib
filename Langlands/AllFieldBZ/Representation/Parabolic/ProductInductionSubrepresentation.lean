import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.AllFieldBZ.Representation.Parabolic.InductionSubrepresentation
import Langlands.Representation.Parabolic.ProductInductionSubrepresentation

/-!
# All-field port of `Langlands.Representation.Parabolic.ProductInductionSubrepresentation`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.ProductInductionSubrepresentation` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding NormalizedInducedSurjectivity NormalizedInductionFactorMatchingTheorem NormalizedInductionOutputFiniteLength NormalizedInductionOutputMatching NormalizedInductionSourceMatching nonempty_valueQuotient_equiv_induced normalizedInducedSubrepresentation normalizedInducedSubrepresentation_bot normalizedInducedSubrepresentation_le_iff normalizedInducedSubrepresentation_ne_bot normalizedInducedSubrepresentation_top normalizedInducedSurjectivity_of_smoothInductionSurjectivity normalizedInductionFactorMatchingTheorem normalizedInductionFactorMatchingTheorem_of_smoothInductionSurjectivity normalizedInductionObject normalizedInductionOutputMatching_of_surjectivity normalizedProductSlotSubrepresentation normalizedProductSlotSubrepresentation_bot normalizedProductSlotSubrepresentation_ne_bot normalizedProductSlotSubrepresentation_top
open Langlands.GeneralLinear
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
  {V : Fin B.length → Type uV}
  [∀ h, AddCommGroup (V h)] [∀ h, Module ℂ (V h)]
  (ρ : ∀ h, Representation ℂ (GeneralLinear (B.size h) F.Carrier) (V h))
  (j : Fin B.length)

/-- Lift a supplied invariant subspace in an original block factor to the
actual normalized product, retaining the original block shape and actions. -/
def normalizedProductSlotSubrepresentation (S : Subrepresentation (ρ j)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Subrepresentation (T.normalizedProductInduced B ρ) :=
  normalizedInducedSubrepresentation T B (B.blockTensor ρ)
    (FiniteTensor.externalSlotSubrepresentation ρ j S)

@[simp]
theorem normalizedProductSlotSubrepresentation_bot :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    normalizedProductSlotSubrepresentation T B ρ j ⊥ = ⊥ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  unfold normalizedProductSlotSubrepresentation
  rw [FiniteTensor.externalSlotSubrepresentation_bot,
    normalizedInducedSubrepresentation_bot]
  rfl

@[simp]
theorem normalizedProductSlotSubrepresentation_top :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    normalizedProductSlotSubrepresentation T B ρ j ⊤ = ⊤ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  unfold normalizedProductSlotSubrepresentation
  rw [FiniteTensor.externalSlotSubrepresentation_top,
    normalizedInducedSubrepresentation_top]
  rfl

/-- A nonzero invariant slot subspace remains nonzero in the actual normalized
product when the complementary carriers are nonzero and all factors smooth. -/
theorem normalizedProductSlotSubrepresentation_ne_bot
    (hV : ∀ h : ({j}ᶜ : Set (Fin B.length)), Nontrivial (V h))
    (S : Subrepresentation (ρ j)) (hS : S ≠ ⊥) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (∀ h, IsSmooth (ρ h)) →
      normalizedProductSlotSubrepresentation T B ρ j S ≠ ⊥ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hρ
  exact normalizedInducedSubrepresentation_ne_bot T B (B.blockTensor ρ) _
    (FiniteTensor.externalSlotSubrepresentation_ne_bot ρ j hV S hS)
    (FiniteTensor.isSmooth_external ρ hρ)

end Langlands.AllFieldBZ.Parabolic
