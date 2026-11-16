import Langlands.Representation.Plancherel.LeviNormalizedProductCoefficients
import Langlands.Representation.Plancherel.CompactProductInducedForm

/-! # Compact probability coefficients in the positive Levi normalization -/

noncomputable section

open MeasureTheory Langlands.Aubert.General
open scoped TensorProduct NNReal

namespace Langlands.Plancherel.CompactInduction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)

/-- Restrict the original positive-Levi diagonal contraction to the given K. -/
def leviIntegrand (g : G) :
    leviProductInducedCoefficientObject h hU A →ₗ[ℂ] (K → ℂ) where
  toFun F k := leviProductInducedCoefficientIntegrand h hU A g F
    ⟨k, Subgroup.mem_top _⟩
  map_add' F J := by
    funext k
    exact congrFun (map_add (leviProductInducedCoefficientIntegrand h hU A g) F J) _
  map_smul' c F := by
    funext k
    exact congrFun (map_smul (leviProductInducedCoefficientIntegrand h hU A g) c F) _

variable [SecondCountableTopology G] (huni : IsUnimodularModulus U hU)

/-- Value preservation holds before integration, on the supplied compact K. -/
@[simp]
theorem leviIntegrand_compare_symm
    (F : leviProductInducedCoefficientObject h hU A) (g : G) :
    integrand h hU A K g ((productInducedCoefficientLeviEquiv h hU A huni).symm F) =
      leviIntegrand h hU A K g F := by
  funext k
  exact congrFun
    (leviProductInducedCoefficientIntegrand_compare_symm h hU A huni F g)
    ⟨k, Subgroup.mem_top _⟩

section TensorNormalization

variable [CompactSpace (Induction.LeftQuotient P)]

/-- The inverse normalization comparison respects the actual product tensor
map, including tensors that are not pure. -/
theorem productInducedCoefficientLeviEquiv_symm_tensor
    (t : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A ⊗[ℂ]
      (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) :
    (productInducedCoefficientLeviEquiv h hU A huni).symm
        (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient t) =
      normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        ((externalInductionLeviEquiv h h hU hU huni huni A A.contragredient).symm t) := by
  change (productInducedCoefficientLeviEquiv h hU A huni).symm
    ((productInducedCoefficientLeviEquiv h hU A huni)
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        ((externalInductionLeviEquiv h h hU hU huni huni A A.contragredient).symm t))) = _
  exact Representation.Equiv.symm_apply_apply _ _

end TensorNormalization

variable [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (hK : IsCompact (K : Set G))

include huni in
omit [T2Space G] in
/-- Every source-normalized diagonal contraction is integrable for the exact
compact probability measure. -/
theorem leviIntegrand_integrable
    (F : leviProductInducedCoefficientObject h hU A) (g : G) :
    Integrable (leviIntegrand h hU A K g F) (measure K hK) := by
  rw [← leviIntegrand_compare_symm h hU A K huni F g]
  exact integrand_integrable h hU A K hK
    ((productInducedCoefficientLeviEquiv h hU A huni).symm F) g

variable [LocallyCompactSpace P]
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (hA : A.IsAdmissible)

/-- Actual coefficient tensors, using the compact probability duality and the
value-preserving positive-Levi comparison. -/
def leviCoefficientTensorEquiv :
    Representation.Equiv
      (leviProductInducedCoefficientObject h hU A).representation
      (coefficientTensorAction ((normalizedInductionFunctor h hU).obj A)) :=
  (productInducedCoefficientLeviEquiv h hU A huni).symm.trans
    (coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hA)

/-- The exact compact probability coefficient map on the positive-Levi carrier. -/
def leviCoefficientMap :
    leviProductInducedCoefficientObject h hU A →ₗ[ℂ] LocallyConstant G ℂ :=
  (coefficientMap h hU A K hK hP hm hPK hG hδ hA).comp
    (productInducedCoefficientLeviEquiv h hU A huni).symm.toLinearMap

/-- Both descriptions use the same compact probability duality. -/
theorem leviCoefficientMap_eq :
    leviCoefficientMap h hU A K huni hK hP hm hPK hG hδ hA =
      (normalizedCoefficientMap h hU A).comp
        (leviCoefficientTensorEquiv h hU A K huni hK hP hm hPK hG hδ hA).toLinearMap := rfl

/-- This normalization comparison preserves the entire coefficient map. -/
@[simp]
theorem leviCoefficientMap_compare
    (F : productInducedCoefficientObject h hU A) :
    leviCoefficientMap h hU A K huni hK hP hm hPK hG hδ hA
        (productInducedCoefficientLeviEquiv h hU A huni F) =
      coefficientMap h hU A K hK hP hm hPK hG hδ hA F := by
  change coefficientMap h hU A K hK hP hm hPK hG hδ hA
    ((productInducedCoefficientLeviEquiv h hU A huni).symm
      (productInducedCoefficientLeviEquiv h hU A huni F)) = _
  rw [Representation.Equiv.symm_apply_apply]

/-- The coefficient is the integral of the original diagonal contraction
against the fixed K Haar probability, for every source vector. -/
theorem leviCoefficientMap_integral
    (F : leviProductInducedCoefficientObject h hU A) (g : G) :
    leviCoefficientMap h hU A K huni hK hP hm hPK hG hδ hA F g =
      ∫ k : K, leviIntegrand h hU A K g F k ∂measure K hK := by
  exact (coefficientMap_integral h hU A K hK hP hm hPK hG hδ hA
    ((productInducedCoefficientLeviEquiv h hU A huni).symm F) g).trans
      (congrArg (fun φ : K → ℂ => ∫ k, φ k ∂measure K hK)
        (leviIntegrand_compare_symm h hU A K huni F g))

section PureTensors

variable [CompactSpace (Induction.LeftQuotient P)]

/-- The compact probability formula in the actual positive-Levi tensor model. -/
theorem leviCoefficientMap_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient)
    (g : G) :
    leviCoefficientMap h hU A K huni hK hP hm hPK hG hδ hA
        (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
          (f ⊗ₜ[ℂ] ℓ)) g =
      ∫ k : K, smoothDualPairing A.representation
        (Induction.eval P (leviInflatedInducingRepresentation h hU A.contragredient) ℓ k)
        (Induction.eval P (leviInflatedInducingRepresentation h hU A) f ((k : G) * g))
        ∂measure K hK := by
  rw [leviCoefficientMap_integral]
  apply integral_congr_ae
  filter_upwards [] with k
  exact congrArg (TensorProduct.lift (smoothDualPairing A.representation).flip)
    (leviNormalizedProductInductionTensorEquiv_tmul_eval h h hU hU huni huni
      A A.contragredient f ℓ ((k : G) * g, k))

end PureTensors

/-- The source's G x G action has the right and inverse-left coefficient law. -/
theorem leviCoefficientMap_action
    (x : G × G) (F : leviProductInducedCoefficientObject h hU A) (g : G) :
    leviCoefficientMap h hU A K huni hK hP hm hPK hG hδ hA
        ((leviProductInducedCoefficientObject h hU A).representation x F) g =
      leviCoefficientMap h hU A K huni hK hP hm hPK hG hδ hA F
        (x.2⁻¹ * g * x.1) := by
  let E := productInducedCoefficientLeviEquiv h hU A huni
  have he : E.symm ((leviProductInducedCoefficientObject h hU A).representation x F) =
      (productInducedCoefficientObject h hU A).representation x (E.symm F) :=
    congrArg (fun T : leviProductInducedCoefficientObject h hU A →ₗ[ℂ]
      productInducedCoefficientObject h hU A => T F) (E.symm.isIntertwining' x)
  change coefficientMap h hU A K hK hP hm hPK hG hδ hA
    (E.symm ((leviProductInducedCoefficientObject h hU A).representation x F)) g = _
  rw [he, coefficientMap_action]
  rfl

/-- The coefficient is bi-invariant under an actual open subgroup. -/
theorem leviCoefficientMap_biInvariant
    (F : leviProductInducedCoefficientObject h hU A) :
    ∃ L : OpenSubgroup G, ∀ (k l : L) (g : G),
      leviCoefficientMap h hU A K huni hK hP hm hPK hG hδ hA F
          ((k : G) * g * (l : G)) =
        leviCoefficientMap h hU A K huni hK hP hm hPK hG hδ hA F g :=
  coefficientMap_biInvariant h hU A K hK hP hm hPK hG hδ hA
    ((productInducedCoefficientLeviEquiv h hU A huni).symm F)

section Forms

open HarishChandraSchwartz

omit [T2Space G]

variable (hcof : CompactOpenCofinal M)

/-- The two compact probability forms on the positive-Levi product carrier. -/
def leviProductForm (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm (leviProductInducedCoefficientObject h hU A).representation :=
  (productForm h hU hP K hK hPK hG hδ A hcof hA b).ofEquiv
    (productInducedCoefficientLeviEquiv h hU A huni).symm

/-- Changing the inducing positive form does not change the product form when
the inducing representation itself is irreducible admissible. -/
theorem leviProductForm_independent (hi : A.representation.IsIrreducible)
    (b c : InvariantPositiveForm A.representation) :
    leviProductForm h hU A K huni hK hP hPK hG hδ hA hcof b =
      leviProductForm h hU A K huni hK hP hPK hG hδ hA hcof c := by
  unfold leviProductForm
  rw [productForm_independent h hU hP K hK hPK hG hδ A hcof hA hi b c]

section PureTensors

variable [CompactSpace (Induction.LeftQuotient P)]

/-- The positive-Levi tensor form is the product of the same two compact
probability forms, expressed through value-preserving normalization. -/
theorem leviProductForm_inner_tensor
    (b : InvariantPositiveForm A.representation)
    (f j : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ m : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) :
    (leviProductForm h hU A K huni hK hP hPK hG hδ hA hcof b).inner
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
        (f ⊗ₜ[ℂ] ℓ))
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
        (j ⊗ₜ[ℂ] m)) =
      (invariantPositiveForm h hU hP K hK hPK hG hδ A b).inner
        ((normalizedInductionLeviEquiv h hU huni A).symm f)
        ((normalizedInductionLeviEquiv h hU huni A).symm j) *
      (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
        (dualInvariantForm b hcof hA)).inner
        ((normalizedInductionLeviEquiv h hU huni A.contragredient).symm ℓ)
        ((normalizedInductionLeviEquiv h hU huni A.contragredient).symm m) := by
  change (productForm h hU hP K hK hPK hG hδ A hcof hA b).inner
    ((productInducedCoefficientLeviEquiv h hU A huni).symm
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
        (f ⊗ₜ[ℂ] ℓ)))
    ((productInducedCoefficientLeviEquiv h hU A huni).symm
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
        (j ⊗ₜ[ℂ] m))) = _
  rw [productInducedCoefficientLeviEquiv_symm_tensor,
    productInducedCoefficientLeviEquiv_symm_tensor,
    externalInductionLeviEquiv_symm_tmul, externalInductionLeviEquiv_symm_tmul]
  exact productForm_inner_tensor h hU hP K hK hPK hG hδ A hcof hA b
    ((normalizedInductionLeviEquiv h hU huni A).symm f)
    ((normalizedInductionLeviEquiv h hU huni A).symm j)
    ((normalizedInductionLeviEquiv h hU huni A.contragredient).symm ℓ)
    ((normalizedInductionLeviEquiv h hU huni A.contragredient).symm m)

end PureTensors

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μ)
  (hi : A.representation.IsIrreducible)

/-- The source's inverse-formal-degree form, with the actual quotient Haar
measure and the same fixed compact probability. -/
def leviFormalDegreeProductForm :
    InvariantPositiveForm (leviProductInducedCoefficientObject h hU A).representation :=
  (formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).ofEquiv
    (productInducedCoefficientLeviEquiv h hU A huni).symm

/-- The actual Levi normalization preserves this entire inverse-degree form. -/
@[simp]
theorem leviFormalDegreeProductForm_compare
    (F J : productInducedCoefficientObject h hU A) :
    (leviFormalDegreeProductForm h hU A K huni hK hP hPK hG hδ hcof C hC μ hsq hi).inner
        (productInducedCoefficientLeviEquiv h hU A huni F)
        (productInducedCoefficientLeviEquiv h hU A huni J) =
      (formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).inner F J := by
  change (formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).inner
    ((productInducedCoefficientLeviEquiv h hU A huni).symm
      (productInducedCoefficientLeviEquiv h hU A huni F))
    ((productInducedCoefficientLeviEquiv h hU A huni).symm
      (productInducedCoefficientLeviEquiv h hU A huni J)) = _
  rw [Representation.Equiv.symm_apply_apply, Representation.Equiv.symm_apply_apply]

/-- The formal degree supplies exactly the source's inverse scaling factor. -/
theorem leviFormalDegreeProductForm_eq (b : InvariantPositiveForm A.representation) :
    leviFormalDegreeProductForm h hU A K huni hK hP hPK hG hδ hcof C hC μ hsq hi =
      (leviProductForm h hU A K huni hK hP hPK hG hδ hsq.1 hcof b).rescale
        (representationFormalDegree C hC μ hcof hsq hi)⁻¹
        (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi)) := by
  apply InvariantPositiveForm.ext_inner
  intro F J
  change (formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).inner
    ((productInducedCoefficientLeviEquiv h hU A huni).symm F)
    ((productInducedCoefficientLeviEquiv h hU A huni).symm J) = _
  rw [formalDegreeProductForm_eq h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi b]
  rfl

section PureTensors

variable [CompactSpace (Induction.LeftQuotient P)]

/-- Waldspurger's inverse-degree pure tensor formula in the positive-Levi model. -/
theorem leviFormalDegreeProductForm_inner_tensor
    (b : InvariantPositiveForm A.representation)
    (f j : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ m : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) :
    (leviFormalDegreeProductForm h hU A K huni hK hP hPK hG hδ hcof C hC μ hsq hi).inner
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
        (f ⊗ₜ[ℂ] ℓ))
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
        (j ⊗ₜ[ℂ] m)) =
      (representationFormalDegree C hC μ hcof hsq hi : ℂ)⁻¹ *
      (invariantPositiveForm h hU hP K hK hPK hG hδ A b).inner
        ((normalizedInductionLeviEquiv h hU huni A).symm f)
        ((normalizedInductionLeviEquiv h hU huni A).symm j) *
      (invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
        (dualInvariantForm b hcof hsq.1)).inner
        ((normalizedInductionLeviEquiv h hU huni A.contragredient).symm ℓ)
        ((normalizedInductionLeviEquiv h hU huni A.contragredient).symm m) := by
  change (formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).inner
    ((productInducedCoefficientLeviEquiv h hU A huni).symm
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
        (f ⊗ₜ[ℂ] ℓ)))
    ((productInducedCoefficientLeviEquiv h hU A huni).symm
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
        (j ⊗ₜ[ℂ] m))) = _
  rw [productInducedCoefficientLeviEquiv_symm_tensor,
    productInducedCoefficientLeviEquiv_symm_tensor,
    externalInductionLeviEquiv_symm_tmul, externalInductionLeviEquiv_symm_tmul]
  exact formalDegreeProductForm_inner_tensor h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi b
    ((normalizedInductionLeviEquiv h hU huni A).symm f)
    ((normalizedInductionLeviEquiv h hU huni A).symm j)
    ((normalizedInductionLeviEquiv h hU huni A.contragredient).symm ℓ)
    ((normalizedInductionLeviEquiv h hU huni A.contragredient).symm m)

end PureTensors

variable [T2Space G] (hcofG : CompactOpenCofinal G)

/-- The exact coefficient-tensor equivalence also preserves the compact
product form, without induced irreducibility. -/
theorem leviProductForm_eq_coefficientForm
    (b : InvariantPositiveForm A.representation) :
    leviProductForm h hU A K huni hK hP hPK hG hδ hA hcof b =
      (coefficientTensorInvariantForm ((normalizedInductionFunctor h hU).obj A)
        hcofG (induced_isAdmissible h hU K hK hPK A hm hA)
        (invariantPositiveForm h hU hP K hK hPK hG hδ A b)).ofEquiv
          (leviCoefficientTensorEquiv h hU A K huni hK hP hm hPK hG hδ hA) := by
  unfold leviProductForm
  rw [productForm_eq_coefficientForm h hU hP K hK hPK hG hδ A hcof hm hcofG hA b]
  rfl

end Forms

end Langlands.Plancherel.CompactInduction
