import Langlands.Representation.Parabolic.InductionFactorMatchingProof
import Langlands.Representation.Filtration.IrreducibleEmbedding

/-! Actual normalized induced filtrations and their graded representations. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- Filter the actual normalized induction by requiring values to lie in the
steps of the supplied Levi filtration. No simplicity of the steps is required. -/
def normalizedInductionFiltration (σ : Representation ℂ (B.Levi F.Carrier) V)
    {m : ℕ} (s : ObjectRepFiltration (Rep.of σ) m) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ObjectRepFiltration (Rep.of (T.normalizedParabolicInduced B σ)) m := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact Induction.valueFiltration (B.parabolic F.Carrier)
    (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
    (fun i => (s.subrepresentation i).toSubmodule)
    (fun _ _ h => s.monotone_subrepresentation h)
    (congrArg Subrepresentation.toSubmodule s.subrepresentation_zero)
    (congrArg Subrepresentation.toSubmodule s.subrepresentation_last)

@[simp]
theorem normalizedInductionFiltration_subrepresentation
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    {m : ℕ} (s : ObjectRepFiltration (Rep.of σ) m) (i : Fin (m + 1)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (normalizedInductionFiltration T B σ s).subrepresentation i =
      Induction.valueSubrep (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
        (s.subrepresentation i).toSubmodule := rfl

/-- For a smooth Levi representation `σ`, a graded piece of the induced filtration
is the actual normalized induction of any smooth representation equivalent to the
corresponding Levi quotient. -/
theorem nonempty_normalizedInductionFiltrationGradedEquiv
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    {m : ℕ} (s : ObjectRepFiltration (Rep.of σ) m) (i : Fin m)
    (π : Representation ℂ (B.Levi F.Carrier) X) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth σ → IsSmooth π → (s.gradedRepresentation i).ρ.Equiv π →
      Nonempty (((normalizedInductionFiltration T B σ s).gradedRepresentation i).ρ.Equiv
        (T.normalizedParabolicInduced B π)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hσ hπ e
  exact nonempty_valueQuotient_equiv_induced T B σ s i π
    (normalizedInducedSurjectivity_of_smoothInductionSurjectivity T B
      Induction.smoothInductionSurjectivity) hσ hπ e

/-- For a smooth Levi representation `σ`, the actual graded representation of
normalized induction is equivalent to the normalized induction of the actual
graded representation. -/
def normalizedInductionFiltrationGradedEquiv
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    {m : ℕ} (s : ObjectRepFiltration (Rep.of σ) m) (i : Fin m) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth σ →
      ((normalizedInductionFiltration T B σ s).gradedRepresentation i).ρ.Equiv
        (T.normalizedParabolicInduced B (s.gradedRepresentation i).ρ) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  intro hσ
  have hgraded : IsSmooth (s.gradedRepresentation i).ρ :=
    isSmooth_of_surjective (s.gradedProjection i).hom (s.gradedProjection_surjective i)
      (isSmooth_of_injective (FactorMatchingProof.subrepInclusion _)
        Subtype.val_injective hσ)
  exact Classical.choice
    (nonempty_normalizedInductionFiltrationGradedEquiv T B σ s i _
      hσ hgraded (Representation.Equiv.refl _))

/-- An irreducible representation embedded in the normalized induction of a
filtered smooth Levi representation embeds in the induction of an actual
graded quotient. The quotient need not be irreducible or nonzero. -/
theorem exists_injective_normalizedInduced_graded
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    {m : ℕ} (s : ObjectRepFiltration (Rep.of σ) m)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) W) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth σ → ρ.IsIrreducible →
      ∀ f : ρ.IntertwiningMap (T.normalizedParabolicInduced B σ),
        Function.Injective f →
          ∃ i : Fin m,
            ∃ g : ρ.IntertwiningMap
              (T.normalizedParabolicInduced B (s.gradedRepresentation i).ρ),
              Function.Injective g := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hσ hρ f hf
  obtain ⟨i, g, hg⟩ :=
    (normalizedInductionFiltration T B σ s).exists_injective_graded f hρ hf
  let e := normalizedInductionFiltrationGradedEquiv T B σ s i hσ
  exact ⟨i, e.toIntertwiningMap.comp g, e.injective.comp hg⟩

end Langlands.Parabolic
