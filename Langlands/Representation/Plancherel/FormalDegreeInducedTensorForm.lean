import Langlands.Representation.Plancherel.InducedTensorForm
import Langlands.Representation.Unitary.AdmissibleFormUniqueness
import Langlands.Representation.Plancherel.FormalDegreeComparisons

/-!
# Formal-degree normalization of actual induced tensor forms

The tensor product of the two actual induced forms is independent of the
arbitrary positive inducing form. The selected normalized tensor form uses the
proved positive Schur formal degree and computes using every positive inducing
form. The individual induced forms scale reciprocally.
-/

noncomputable section

open MeasureTheory
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G)) [LocallyCompactSpace P]
  [CompactSpace (Induction.LeftQuotient P)]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (A : SmoothRep.{0, uG, uV} ℂ M) (hcof : CompactOpenCofinal M)

/-- The actual two-induced-factor tensor form is independent of every choice
of invariant positive inducing form when the inducing representation is
irreducible admissible. -/
theorem normalizedInducedDualTensorForm_independent
    (hA : IsAdmissible A.representation) (hi : A.representation.IsIrreducible)
    (b c : InvariantPositiveForm A.representation) :
    normalizedInducedDualTensorForm h hU hP hG hδ A hcof hA b =
      normalizedInducedDualTensorForm h hU hP hG hδ A hcof hA c := by
  obtain ⟨a, ha, rfl⟩ := b.exists_pos_rescale_eq c hcof hA hi
  exact (normalizedInducedDualTensorForm_rescale h hU hP hG hδ A hcof hA b a ha).symm

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μ)
  (hi : A.representation.IsIrreducible)

/-- The actual positive induced tensor form with inverse Schur formal-degree
normalization. An inducing form exists by the proved unitarizability theorem;
its arbitrary selection is removed by the computation theorem below. -/
def formalDegreeInducedTensorForm :
    InvariantPositiveForm (normalizedInductionDualTensorAction h hU A) :=
  let b := Classical.choice
    (isUnitarizable_of_isSquareIntegrableModCentralSubgroup C hC μ hcof hsq)
  (normalizedInducedDualTensorForm h hU hP hG hδ A hcof hsq.1 b).rescale
    (representationFormalDegree C hC μ hcof hsq hi)⁻¹
    (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi))

/-- The selected normalized form equals the construction from every actual
invariant positive inducing form, using the same degree and measures. -/
theorem formalDegreeInducedTensorForm_eq
    (b : InvariantPositiveForm A.representation) :
    formalDegreeInducedTensorForm h hU hP hG hδ A hcof C hC μ hsq hi =
      (normalizedInducedDualTensorForm h hU hP hG hδ A hcof hsq.1 b).rescale
        (representationFormalDegree C hC μ hcof hsq hi)⁻¹
        (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi)) := by
  unfold formalDegreeInducedTensorForm
  exact congrArg
    (fun B : InvariantPositiveForm (normalizedInductionDualTensorAction h hU A) =>
      B.rescale (representationFormalDegree C hC μ hcof hsq hi)⁻¹
        (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi)))
    (normalizedInducedDualTensorForm_independent h hU hP hG hδ A hcof hsq.1 hi _ b)

/-- The source inverse-degree product formula holds with every actual
invariant positive inducing form on pure tensors. -/
theorem formalDegreeInducedTensorForm_inner_tmul
    (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A)
    (ℓ m : (normalizedInductionFunctor h hU).obj A.contragredient) :
    (formalDegreeInducedTensorForm h hU hP hG hδ A hcof C hC μ hsq hi).inner
        (f ⊗ₜ[ℂ] ℓ) (j ⊗ₜ[ℂ] m) =
      (representationFormalDegree C hC μ hcof hsq hi : ℂ)⁻¹ *
        (compactQuotientNormalizedInductionForm h hU hP hG hδ A b).inner f j *
          (compactQuotientNormalizedInductionForm h hU hP hG hδ A.contragredient
            (dualInvariantForm b hcof hsq.1)).inner ℓ m := by
  rw [formalDegreeInducedTensorForm_eq h hU hP hG hδ A hcof C hC μ hsq hi b,
    InvariantPositiveForm.rescale_inner, normalizedInducedDualTensorForm_inner_tmul,
    Complex.ofReal_inv, mul_assoc]

end Langlands.Plancherel
