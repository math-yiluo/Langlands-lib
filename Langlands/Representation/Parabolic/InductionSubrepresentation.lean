import Langlands.Representation.Parabolic.InductionFactorMatchingProof

/-! Smooth induction detects actual invariant subspaces by compact local sections. -/

noncomputable section

namespace Langlands.Induction

universe uK uG uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
  {V : Type uV} [AddCommGroup V] [Module k V]

/-- Every vector in an invariant subspace occurs at the identity of a smooth
induced function all of whose values lie in that subspace. -/
theorem exists_valueSubrep_eval (P : Subgroup G) (ρ : Representation k P V)
    (hρ : IsSmooth ρ) (S : Subrepresentation ρ) (v : S.toSubmodule) :
    ∃ f : SmoothFunctions P ρ, f ∈ valueSubrep P ρ S.toSubmodule ∧
      eval P ρ f 1 = (v : V) := by
  let i := FactorMatchingProof.subrepInclusion S
  have hS : IsSmooth S.toRepresentation :=
    isSmooth_of_injective i Subtype.val_injective hρ
  let c := compactLocalSection P S.toRepresentation hS 1 v Set.univ
    isOpen_univ (Set.mem_univ _)
  refine ⟨smoothInducedMap P i c.val, ?_, ?_⟩
  · intro x
    exact (eval P S.toRepresentation c.val x).property
  · change ((eval P S.toRepresentation c.val 1 : S.toSubmodule) : V) = (v : V)
    exact congrArg Subtype.val
      (compactLocalSection_apply P S.toRepresentation hS 1 v Set.univ
        isOpen_univ (Set.mem_univ _))

/-- For a smooth inducing representation, the value subrepresentation
construction reflects the inclusion relation on actual invariant subspaces. -/
theorem valueSubrep_le_iff (P : Subgroup G) (ρ : Representation k P V)
    (hρ : IsSmooth ρ) (S U : Subrepresentation ρ) :
    valueSubrep P ρ S.toSubmodule ≤ valueSubrep P ρ U.toSubmodule ↔ S ≤ U := by
  constructor
  · intro h v hv
    obtain ⟨f, hf, he⟩ := exists_valueSubrep_eval P ρ hρ S ⟨v, hv⟩
    have hv' := h hf 1
    rw [he] at hv'
    exact hv'
  · intro h
    exact valueSubrep_mono P ρ h

end Langlands.Induction

namespace Langlands.Parabolic

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
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

private def normalizedInducingSubrepresentation (S : Subrepresentation σ) :
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

/-- A proper invariant Levi subspace gives a proper actual induced subspace. -/
theorem normalizedInducedSubrepresentation_ne_top
    (S : Subrepresentation σ) (hS : S ≠ ⊤) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth σ → normalizedInducedSubrepresentation T B σ S ≠ ⊤ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hσ h
  apply hS
  apply le_antisymm le_top
  apply (normalizedInducedSubrepresentation_le_iff T B σ ⊤ S hσ).mp
  rw [h, normalizedInducedSubrepresentation_top]

end Langlands.Parabolic
