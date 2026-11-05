import Langlands.Representation.Plancherel.CompactInducedHermitianForm
import Langlands.Representation.Plancherel.CoefficientTensorForm
import Langlands.Representation.Plancherel.FormalDegreeComparisons
import Langlands.Representation.Unitary.AdmissibleFormUniqueness

/-!
# Compact probability and formal degree on actual induced tensors

Both actual induced factors use the same compact Haar probability. Reciprocal
dual scaling removes the choice of the positive inducing form.
-/

noncomputable section

open MeasureTheory
open scoped TensorProduct NNReal

namespace Langlands.Plancherel.CompactInduction

open Aubert.General HarishChandraSchwartz

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (A : SmoothRep.{0, uG, uV} ℂ M) (hcof : CompactOpenCofinal M)

/-- The positive tensor form on the two actual normalized inductions, using
the supplied compact Haar probability in each factor. -/
def tensorForm (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm (normalizedInductionDualTensorAction h hU A) :=
  (invariantPositiveForm h hU hP K hK hPK hG hδ A b).tensorProduct
    (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
      (dualInvariantForm b hcof hA))

@[simp]
theorem tensorForm_inner_tmul (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A)
    (ℓ m : (normalizedInductionFunctor h hU).obj A.contragredient) :
    (tensorForm h hU hP K hK hPK hG hδ A hcof hA b).inner
      (f ⊗ₜ[ℂ] ℓ) (j ⊗ₜ[ℂ] m) =
        (invariantPositiveForm h hU hP K hK hPK hG hδ A b).inner f j *
          (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
            (dualInvariantForm b hcof hA)).inner ℓ m :=
  InvariantPositiveForm.tensorProduct_inner_tmul _ _ f j ℓ m

/-- Positive inducing rescaling and reciprocal dual rescaling cancel on the
entire tensor with the compact measure fixed. -/
theorem tensorForm_rescale (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation) (a : ℝ) (ha : 0 < a) :
    tensorForm h hU hP K hK hPK hG hδ A hcof hA (b.rescale a ha) =
      tensorForm h hU hP K hK hPK hG hδ A hcof hA b := by
  have hd :
      invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
          (dualInvariantForm (b.rescale a ha) hcof hA) =
        (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
          (dualInvariantForm b hcof hA)).rescale a⁻¹ (inv_pos.mpr ha) := by
    calc
      _ = invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
          ((dualInvariantForm b hcof hA).rescale a⁻¹ (inv_pos.mpr ha)) :=
        congrArg (fun c : InvariantPositiveForm A.contragredient.representation =>
          invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient c)
          (dualInvariantForm_rescale hcof hA b a ha)
      _ = _ := invariantPositiveForm_rescale h hU hP K hK hPK hG hδ
        A.contragredient (dualInvariantForm b hcof hA) a⁻¹ (inv_pos.mpr ha)
  exact (congrArg₂
    (fun (c : InvariantPositiveForm ((normalizedInductionFunctor h hU).obj A).representation)
      (d : InvariantPositiveForm
        ((normalizedInductionFunctor h hU).obj A.contragredient).representation) =>
          c.tensorProduct d)
    (invariantPositiveForm_rescale h hU hP K hK hPK hG hδ A b a ha) hd).trans
      (InvariantPositiveForm.tensorProduct_rescale_inv _ _ a ha)

/-- For irreducible admissible inducing representations the full tensor form
is independent of every invariant positive inducing form. -/
theorem tensorForm_independent (hA : IsAdmissible A.representation)
    (hi : A.representation.IsIrreducible)
    (b c : InvariantPositiveForm A.representation) :
    tensorForm h hU hP K hK hPK hG hδ A hcof hA b =
      tensorForm h hU hP K hK hPK hG hδ A hcof hA c := by
  obtain ⟨a, ha, rfl⟩ := b.exists_pos_rescale_eq c hcof hA hi
  exact (tensorForm_rescale h hU hP K hK hPK hG hδ A hcof hA b a ha).symm

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μ)
  (hi : A.representation.IsIrreducible)

/-- The compact probability tensor form normalized by the inverse of the
actual Schur formal degree, with no inducing form among its inputs. -/
def formalDegreeTensorForm :
    InvariantPositiveForm (normalizedInductionDualTensorAction h hU A) :=
  let b := Classical.choice
    (isUnitarizable_of_isSquareIntegrableModCentralSubgroup C hC μ hcof hsq)
  (tensorForm h hU hP K hK hPK hG hδ A hcof hsq.1 b).rescale
    (representationFormalDegree C hC μ hcof hsq hi)⁻¹
    (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi))

/-- Every actual positive inducing form computes the same selected
formal-degree-normalized compact tensor form. -/
theorem formalDegreeTensorForm_eq (b : InvariantPositiveForm A.representation) :
    formalDegreeTensorForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi =
      (tensorForm h hU hP K hK hPK hG hδ A hcof hsq.1 b).rescale
        (representationFormalDegree C hC μ hcof hsq hi)⁻¹
        (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi)) := by
  unfold formalDegreeTensorForm
  exact congrArg
    (fun B : InvariantPositiveForm (normalizedInductionDualTensorAction h hU A) =>
      B.rescale (representationFormalDegree C hC μ hcof hsq hi)⁻¹
        (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi)))
    (tensorForm_independent h hU hP K hK hPK hG hδ A hcof hsq.1 hi _ b)

/-- The actual inverse-degree product formula on pure tensors, for every
positive inducing form and the fixed compact probability. -/
theorem formalDegreeTensorForm_inner_tmul (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A)
    (ℓ m : (normalizedInductionFunctor h hU).obj A.contragredient) :
    (formalDegreeTensorForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).inner
        (f ⊗ₜ[ℂ] ℓ) (j ⊗ₜ[ℂ] m) =
      (representationFormalDegree C hC μ hcof hsq hi : ℂ)⁻¹ *
        (invariantPositiveForm h hU hP K hK hPK hG hδ A b).inner f j *
          (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
            (dualInvariantForm b hcof hsq.1)).inner ℓ m := by
  rw [formalDegreeTensorForm_eq h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi b,
    InvariantPositiveForm.rescale_inner, tensorForm_inner_tmul,
    Complex.ofReal_inv, mul_assoc]

end Langlands.Plancherel.CompactInduction
