import Langlands.AllFieldBZ.Representation.Parabolic.InductionFactorMatchingProof
import Langlands.Representation.Parabolic.InductionSubrepresentation

/-!
# All-field port of `Langlands.Representation.Parabolic.InductionSubrepresentation`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.InductionSubrepresentation` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Induction
open Langlands.Induction
universe uK uG uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
  {V : Type uV} [AddCommGroup V] [Module k V]

end Langlands.AllFieldBZ.Induction
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding NormalizedInducedSurjectivity NormalizedInductionFactorMatchingTheorem NormalizedInductionOutputFiniteLength NormalizedInductionOutputMatching NormalizedInductionSourceMatching nonempty_valueQuotient_equiv_induced normalizedInducedSubrepresentation normalizedInducedSubrepresentation_bot normalizedInducedSubrepresentation_le_iff normalizedInducedSubrepresentation_ne_bot normalizedInducedSubrepresentation_top normalizedInducedSurjectivity_of_smoothInductionSurjectivity normalizedInductionFactorMatchingTheorem normalizedInductionFactorMatchingTheorem_of_smoothInductionSurjectivity normalizedInductionObject normalizedInductionOutputMatching_of_surjectivity
open Langlands.GeneralLinear
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (B.Levi F.Carrier) V)

/-- The actual normalized induced functions taking values in a supplied Levi
invariant subspace. -/
def normalizedInducedSubrepresentation (S : Subrepresentation σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Subrepresentation (T.normalizedParabolicInduced B σ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.valueSubrep (B.parabolic F.Carrier)
    (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
    S.toSubmodule

@[simp]
theorem normalizedInducedSubrepresentation_bot :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    normalizedInducedSubrepresentation T B σ ⊥ = ⊥ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact Induction.valueSubrep_bot _ _

@[simp]
theorem normalizedInducedSubrepresentation_top :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    normalizedInducedSubrepresentation T B σ ⊤ = ⊤ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact Induction.valueSubrep_top _ _

private def _root_.Langlands.Parabolic.normalizedInducingSubrepresentation (S : Subrepresentation σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Subrepresentation
      (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g _ hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hv) }

/-- Actual normalized induction reflects inclusion of invariant Levi subspaces
when the inducing representation is smooth. -/
theorem normalizedInducedSubrepresentation_le_iff
    (S U : Subrepresentation σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth σ →
      (normalizedInducedSubrepresentation T B σ S ≤
        normalizedInducedSubrepresentation T B σ U ↔ S ≤ U) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  intro hσ
  have hτ : IsSmooth
      (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) :=
    (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).2
      (isSmooth_comp _ (B.leviProjectionContinuous F.Carrier).continuous hσ)
  exact Induction.valueSubrep_le_iff (B.parabolic F.Carrier) _ hτ
    (normalizedInducingSubrepresentation T B σ S)
    (normalizedInducingSubrepresentation T B σ U)

/-- A nonzero invariant Levi subspace gives a nonzero actual induced subspace. -/
theorem normalizedInducedSubrepresentation_ne_bot
    (S : Subrepresentation σ) (hS : S ≠ ⊥) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth σ → normalizedInducedSubrepresentation T B σ S ≠ ⊥ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hσ h
  apply hS
  apply le_antisymm _ bot_le
  apply (normalizedInducedSubrepresentation_le_iff T B σ S ⊥ hσ).mp
  rw [h, normalizedInducedSubrepresentation_bot]

end Langlands.AllFieldBZ.Parabolic
