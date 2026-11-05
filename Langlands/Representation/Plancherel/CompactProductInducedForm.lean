import Langlands.Representation.Plancherel.CompactInducedTensorForm
import Langlands.Representation.Plancherel.CompactInducedDualIsometry
import Langlands.Representation.Plancherel.CompactProductInducedCoefficients

/-!
# Compact Hermitian forms on the actual product-induced coefficient source

The existing product-induction and compact integral duality equivalences
identify the source form with the canonical coefficient-tensor form.
-/

noncomputable section

set_option maxHeartbeats 800000

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

/-- Transfer the two compact probability forms to the original
product-induced function carrier by the existing product comparison. -/
def productForm (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm (productInducedCoefficientObject h hU A).representation := by
  letI : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK hPK
  exact (tensorForm h hU hP K hK hPK hG hδ A hcof hA b).ofEquiv
    (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm

section PureTensors

variable [CompactSpace (Induction.LeftQuotient P)]

/-- The source form is the product of the two exact compact-induced
pairings on pointwise product sections. -/
theorem productForm_inner_tensor (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A)
    (ℓ m : (normalizedInductionFunctor h hU).obj A.contragredient) :
    (productForm h hU hP K hK hPK hG hδ A hcof hA b).inner
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        (f ⊗ₜ[ℂ] ℓ))
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        (j ⊗ₜ[ℂ] m)) =
      (invariantPositiveForm h hU hP K hK hPK hG hδ A b).inner f j *
        (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
          (dualInvariantForm b hcof hA)).inner ℓ m := by
  change (tensorForm h hU hP K hK hPK hG hδ A hcof hA b).inner
    ((normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        (f ⊗ₜ[ℂ] ℓ)))
    ((normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        (j ⊗ₜ[ℂ] m))) = _
  rw [Representation.Equiv.symm_apply_apply, Representation.Equiv.symm_apply_apply,
    tensorForm_inner_tmul]

end PureTensors

/-- Arbitrary positive inducing forms give the same entire source form
when the inducing representation is irreducible admissible. -/
theorem productForm_independent (hA : IsAdmissible A.representation)
    (hi : A.representation.IsIrreducible)
    (b c : InvariantPositiveForm A.representation) :
    productForm h hU hP K hK hPK hG hδ A hcof hA b =
      productForm h hU hP K hK hPK hG hδ A hcof hA c := by
  unfold productForm
  rw [tensorForm_independent h hU hP K hK hPK hG hδ A hcof hA hi b c]

section CoefficientComparison

variable [T2Space G] (hm : Continuous h.projection) (hcofG : CompactOpenCofinal G)

/-- The actual compact dual tensor equivalence preserves the canonical
coefficient-tensor form, without irreducibility of either induction. -/
theorem dualTensorEquiv_form (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation) :
    (coefficientTensorInvariantForm ((normalizedInductionFunctor h hU).obj A)
      hcofG (induced_isAdmissible h hU K hK hPK A hm hA)
      (invariantPositiveForm h hU hP K hK hPK hG hδ A b)).ofEquiv
        (dualTensorEquiv h hU A K hK hP hm hPK hG hδ hA) =
      tensorForm h hU hP K hK hPK hG hδ A hcof hA b := by
  let B := invariantPositiveForm h hU hP K hK hPK hG hδ A b
  let Bd := invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
    (dualInvariantForm b hcof hA)
  let E := integralDualEquiv h hU hP hm K hK hPK hG hδ A hA
  let hI : IsAdmissible ((normalizedInductionFunctor h hU).obj A).representation :=
    induced_isAdmissible h hU K hK hPK A hm hA
  have hd (ℓ m : (normalizedInductionFunctor h hU).obj A.contragredient) :
      (dualInvariantForm B hcofG hI).inner (E.symm ℓ) (E.symm m) =
        Bd.inner ℓ m := by
    have he := congrArg
      (fun c : InvariantPositiveForm
        ((normalizedInductionFunctor h hU).obj A).contragredient.representation =>
          c.inner (E.symm ℓ) (E.symm m))
      (integralDualEquiv_form h hU hP K hK hPK hG hδ A hm hcof hcofG hA b)
    change Bd.inner (E (E.symm ℓ)) (E (E.symm m)) =
      (dualInvariantForm B hcofG hI).inner (E.symm ℓ) (E.symm m) at he
    rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply] at he
    exact he.symm
  apply InvariantPositiveForm.ext_inner
  intro t s
  change (coefficientTensorInvariantForm ((normalizedInductionFunctor h hU).obj A)
    hcofG hI B).inner
      (dualTensorEquiv h hU A K hK hP hm hPK hG hδ hA t)
      (dualTensorEquiv h hU A K hK hP hm hPK hG hδ hA s) =
    (tensorForm h hU hP K hK hPK hG hδ A hcof hA b).inner t s
  induction t using TensorProduct.inductionOn with
  | tmul f ℓ =>
    induction s using TensorProduct.inductionOn with
    | tmul j m =>
      change (coefficientTensorInvariantForm ((normalizedInductionFunctor h hU).obj A)
        hcofG hI B).inner (f ⊗ₜ[ℂ] E.symm ℓ) (j ⊗ₜ[ℂ] E.symm m) = _
      exact (coefficientTensorInvariantForm_inner_tmul
        ((normalizedInductionFunctor h hU).obj A) hcofG hI B
          f j (E.symm ℓ) (E.symm m)).trans
        ((congrArg (fun z : ℂ => B.inner f j * z) (hd ℓ m)).trans
          (tensorForm_inner_tmul h hU hP K hK hPK hG hδ A hcof hA b f j ℓ m).symm)
    | add s s' hs hs' =>
      simp only [map_add, InvariantPositiveForm.add_right, hs, hs']
  | add t t' ht ht' =>
    simp only [map_add, PreInnerProductSpace.Core.add_left, ht, ht']

/-- The original product-induced source form agrees with the canonical
coefficient form through the existing integral coefficient comparison. -/
theorem productForm_eq_coefficientForm (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation) :
    productForm h hU hP K hK hPK hG hδ A hcof hA b =
      (coefficientTensorInvariantForm ((normalizedInductionFunctor h hU).obj A)
        hcofG (induced_isAdmissible h hU K hK hPK A hm hA)
        (invariantPositiveForm h hU hP K hK hPK hG hδ A b)).ofEquiv
          (coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hA) := by
  let : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK hPK
  let N := normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
  apply InvariantPositiveForm.ext_inner
  intro F J
  exact (congrArg
    (fun c : InvariantPositiveForm (normalizedInductionDualTensorAction h hU A) =>
      c.inner (N.symm F) (N.symm J))
    (dualTensorEquiv_form h hU hP K hK hPK hG hδ A hcof hm hcofG hA b)).symm

end CoefficientComparison

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μ)
  (hi : A.representation.IsIrreducible)

/-- The actual inverse-Schur-degree form on the original product-induced
function carrier, without a positive inducing form as input. -/
def formalDegreeProductForm :
    InvariantPositiveForm (productInducedCoefficientObject h hU A).representation := by
  letI : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK hPK
  exact (formalDegreeTensorForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).ofEquiv
    (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm

/-- Every inducing positive form computes the same inverse-degree source
form with the fixed compact probability. -/
theorem formalDegreeProductForm_eq (b : InvariantPositiveForm A.representation) :
    formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi =
      (productForm h hU hP K hK hPK hG hδ A hcof hsq.1 b).rescale
        (representationFormalDegree C hC μ hcof hsq hi)⁻¹
        (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi)) := by
  let : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK hPK
  apply InvariantPositiveForm.ext_inner
  intro F J
  change (formalDegreeTensorForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).inner
    ((normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm F)
    ((normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm J) = _
  rw [formalDegreeTensorForm_eq h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi b]
  rfl

section PureTensors

variable [CompactSpace (Induction.LeftQuotient P)]

/-- Waldspurger's inverse-degree pure-tensor formula on the actual source. -/
theorem formalDegreeProductForm_inner_tensor
    (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A)
    (ℓ m : (normalizedInductionFunctor h hU).obj A.contragredient) :
    (formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).inner
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        (f ⊗ₜ[ℂ] ℓ))
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        (j ⊗ₜ[ℂ] m)) =
      (representationFormalDegree C hC μ hcof hsq hi : ℂ)⁻¹ *
        (invariantPositiveForm h hU hP K hK hPK hG hδ A b).inner f j *
          (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
            (dualInvariantForm b hcof hsq.1)).inner ℓ m := by
  change (formalDegreeTensorForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).inner
    ((normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        (f ⊗ₜ[ℂ] ℓ)))
    ((normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        (j ⊗ₜ[ℂ] m))) = _
  rw [Representation.Equiv.symm_apply_apply, Representation.Equiv.symm_apply_apply]
  exact formalDegreeTensorForm_inner_tmul h hU hP K hK hPK hG hδ A hcof
    C hC μ hsq hi b f j ℓ m

end PureTensors

variable [T2Space G] (hm : Continuous h.projection) (hcofG : CompactOpenCofinal G)

/-- The actual degree-normalized source form is the same inverse-degree
rescaling of the canonical coefficient form through integral duality. -/
theorem formalDegreeProductForm_eq_coefficientForm
    (b : InvariantPositiveForm A.representation) :
    formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi =
      ((coefficientTensorInvariantForm ((normalizedInductionFunctor h hU).obj A)
        hcofG (induced_isAdmissible h hU K hK hPK A hm hsq.1)
        (invariantPositiveForm h hU hP K hK hPK hG hδ A b)).ofEquiv
          (coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hsq.1)).rescale
            (representationFormalDegree C hC μ hcof hsq hi)⁻¹
            (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi)) := by
  rw [formalDegreeProductForm_eq h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi b,
    productForm_eq_coefficientForm h hU hP K hK hPK hG hδ A hcof hm hcofG hsq.1 b]

end Langlands.Plancherel.CompactInduction
