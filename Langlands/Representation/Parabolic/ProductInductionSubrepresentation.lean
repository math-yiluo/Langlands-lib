import Langlands.Representation.Tensor.ExternalSubrepresentation
import Langlands.Representation.Parabolic.InductionSubrepresentation
import Langlands.Representation.Induction.BlockFactors

/-! Actual invariant slot subspaces in normalized block-product induction. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
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

/-- Nonzero complementary carriers and smooth original factors make the
actual normalized slot construction reflect inclusion of invariant subspaces. -/
theorem normalizedProductSlotSubrepresentation_le_iff
    (hV : ∀ h : ({j}ᶜ : Set (Fin B.length)), Nontrivial (V h))
    (S U : Subrepresentation (ρ j)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (∀ h, IsSmooth (ρ h)) →
      (normalizedProductSlotSubrepresentation T B ρ j S ≤
        normalizedProductSlotSubrepresentation T B ρ j U ↔ S ≤ U) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hρ
  exact (normalizedInducedSubrepresentation_le_iff T B (B.blockTensor ρ)
    (FiniteTensor.externalSlotSubrepresentation ρ j S)
    (FiniteTensor.externalSlotSubrepresentation ρ j U)
    (FiniteTensor.isSmooth_external ρ hρ)).trans
      (FiniteTensor.externalSlotSubrepresentation_le_iff ρ j hV S U)

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

/-- A proper invariant slot subspace remains proper in the actual normalized
product under the same hypotheses. -/
theorem normalizedProductSlotSubrepresentation_ne_top
    (hV : ∀ h : ({j}ᶜ : Set (Fin B.length)), Nontrivial (V h))
    (S : Subrepresentation (ρ j)) (hS : S ≠ ⊤) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (∀ h, IsSmooth (ρ h)) →
      normalizedProductSlotSubrepresentation T B ρ j S ≠ ⊤ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hρ
  exact normalizedInducedSubrepresentation_ne_top T B (B.blockTensor ρ) _
    (FiniteTensor.externalSlotSubrepresentation_ne_top ρ j hV S hS)
    (FiniteTensor.isSmooth_external ρ hρ)

/-- A proper nonzero original slot subrepresentation gives an actual proper
nonzero subrepresentation of the full normalized block product. -/
theorem normalizedProductSlotSubrepresentation_proper_nonzero
    (hV : ∀ h : ({j}ᶜ : Set (Fin B.length)), Nontrivial (V h))
    (S : Subrepresentation (ρ j)) (hS₀ : S ≠ ⊥) (hS₁ : S ≠ ⊤) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (∀ h, IsSmooth (ρ h)) →
      normalizedProductSlotSubrepresentation T B ρ j S ≠ ⊥ ∧
        normalizedProductSlotSubrepresentation T B ρ j S ≠ ⊤ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hρ
  exact ⟨normalizedProductSlotSubrepresentation_ne_bot T B ρ j hV S hS₀ hρ,
    normalizedProductSlotSubrepresentation_ne_top T B ρ j hV S hS₁ hρ⟩

end Langlands.Parabolic
