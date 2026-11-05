import Langlands.Representation.Aubert.General.NormalizedInductionUnitarity
import Langlands.Representation.Aubert.General.InductionCarrierTransport
import Langlands.Representation.Plancherel.CoefficientTensorForm
import Langlands.Representation.Plancherel.NormalizedInductionDualTensor

/-!
# Actual induced tensor forms and positive rescaling

Both tensor factors are actual normalized inductions: the second induces the
smooth dual of the inducing representation. Their forms use the literal same
measure choice already made by compactQuotientNormalizedInductionForm.
-/

noncomputable section

open MeasureTheory
open scoped TensorProduct NNReal

namespace Langlands

universe uG uV uW

namespace Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G)) [LocallyCompactSpace P]
  [CompactSpace (Induction.LeftQuotient P)]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))

/-- The existing normalized induced form integrates against its original,
form-independent choice of compact quotient measure. -/
theorem compactQuotientNormalizedInductionForm_inner
    (A : SmoothRep.{0, uG, uV} ℂ M) (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A) :
    (compactQuotientNormalizedInductionForm h hU hP hG hδ A b).inner f j =
      ∫ k : (⊤ : Subgroup G),
        b.inner (Induction.eval P (inducingRepresentation h hU A) f k)
          (Induction.eval P (inducingRepresentation h hU A) j k)
        ∂(Classical.choose (Induction.exists_compactQuotient_measure hG P hP)) := rfl

/-- Positive rescaling commutes with the actual normalized induction form,
with no change to its chosen measure. -/
theorem compactQuotientNormalizedInductionForm_rescale
    (A : SmoothRep.{0, uG, uV} ℂ M) (b : InvariantPositiveForm A.representation)
    (a : ℝ) (ha : 0 < a) :
    compactQuotientNormalizedInductionForm h hU hP hG hδ A (b.rescale a ha) =
      (compactQuotientNormalizedInductionForm h hU hP hG hδ A b).rescale a ha := by
  apply InvariantPositiveForm.ext_inner
  intro f j
  rw [compactQuotientNormalizedInductionForm_inner,
    InvariantPositiveForm.rescale_inner, compactQuotientNormalizedInductionForm_inner]
  simp_rw [InvariantPositiveForm.rescale_inner]
  exact integral_const_mul _ _

/-- Pullback along an inducing equivalence commutes with the same literal
integral form, including for independent carrier universes. -/
theorem compactQuotientNormalizedInductionForm_ofEquiv
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (b : InvariantPositiveForm B.representation)
    (e : A.representation.Equiv B.representation) :
    compactQuotientNormalizedInductionForm h hU hP hG hδ A (b.ofEquiv e) =
      (compactQuotientNormalizedInductionForm h hU hP hG hδ B b).ofEquiv
        (normalizedInductionEquivOfEquiv h hU e) := by
  apply InvariantPositiveForm.ext_inner
  intro f j
  rw [compactQuotientNormalizedInductionForm_inner]
  change _ = (compactQuotientNormalizedInductionForm h hU hP hG hδ B b).inner
    (normalizedInductionEquivOfEquiv h hU e f) (normalizedInductionEquivOfEquiv h hU e j)
  rw [compactQuotientNormalizedInductionForm_inner]
  rfl

end Aubert.General

namespace Plancherel

open Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))

variable [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (hP : IsClosed (P : Set G)) [LocallyCompactSpace P]
  [CompactSpace (Induction.LeftQuotient P)]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (A : SmoothRep.{0, uG, uV} ℂ M) (hcof : CompactOpenCofinal M)
  (hA : IsAdmissible A.representation)

/-- The unnormalized positive form on the two actual induced factors, using
the original inducing form and its actual smooth-dual form. -/
def normalizedInducedDualTensorForm (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm (normalizedInductionDualTensorAction h hU A) :=
  (compactQuotientNormalizedInductionForm h hU hP hG hδ A b).tensorProduct
    (compactQuotientNormalizedInductionForm h hU hP hG hδ A.contragredient
      (HarishChandraSchwartz.dualInvariantForm b hcof hA))

@[simp]
theorem normalizedInducedDualTensorForm_inner_tmul
    (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A)
    (ℓ m : (normalizedInductionFunctor h hU).obj A.contragredient) :
    (normalizedInducedDualTensorForm h hU hP hG hδ A hcof hA b).inner
      (f ⊗ₜ[ℂ] ℓ) (j ⊗ₜ[ℂ] m) =
        (compactQuotientNormalizedInductionForm h hU hP hG hδ A b).inner f j *
          (compactQuotientNormalizedInductionForm h hU hP hG hδ A.contragredient
            (HarishChandraSchwartz.dualInvariantForm b hcof hA)).inner ℓ m :=
  InvariantPositiveForm.tensorProduct_inner_tmul _ _ f j ℓ m

/-- Reciprocal inducing and dual rescalings cancel after both actual
inductions, on the entire induced tensor. -/
theorem normalizedInducedDualTensorForm_rescale
    (b : InvariantPositiveForm A.representation) (a : ℝ) (ha : 0 < a) :
    normalizedInducedDualTensorForm h hU hP hG hδ A hcof hA (b.rescale a ha) =
      normalizedInducedDualTensorForm h hU hP hG hδ A hcof hA b := by
  have hd :
      compactQuotientNormalizedInductionForm h hU hP hG hδ A.contragredient
          (HarishChandraSchwartz.dualInvariantForm (b.rescale a ha) hcof hA) =
        (compactQuotientNormalizedInductionForm h hU hP hG hδ A.contragredient
          (HarishChandraSchwartz.dualInvariantForm b hcof hA)).rescale a⁻¹
            (inv_pos.mpr ha) := by
    calc
      _ = compactQuotientNormalizedInductionForm h hU hP hG hδ A.contragredient
          ((HarishChandraSchwartz.dualInvariantForm b hcof hA).rescale a⁻¹
            (inv_pos.mpr ha)) :=
        congrArg (fun c : InvariantPositiveForm A.contragredient.representation =>
          compactQuotientNormalizedInductionForm h hU hP hG hδ A.contragredient c)
          (HarishChandraSchwartz.dualInvariantForm_rescale hcof hA b a ha)
      _ = _ := compactQuotientNormalizedInductionForm_rescale h hU hP hG hδ
        A.contragredient (HarishChandraSchwartz.dualInvariantForm b hcof hA)
          a⁻¹ (inv_pos.mpr ha)
  exact (congrArg₂
    (fun (c : InvariantPositiveForm ((normalizedInductionFunctor h hU).obj A).representation)
      (d : InvariantPositiveForm
        ((normalizedInductionFunctor h hU).obj A.contragredient).representation) =>
          c.tensorProduct d)
    (compactQuotientNormalizedInductionForm_rescale h hU hP hG hδ A b a ha) hd).trans
      (InvariantPositiveForm.tensorProduct_rescale_inv _ _ a ha)

end Plancherel

end Langlands
