import Langlands.Representation.Plancherel.LeviNormalizedProductInduction
import Langlands.Representation.Plancherel.ProductInducedCoefficients

/-! # Actual product coefficients in the positive Levi normalization -/

noncomputable section

open MeasureTheory Langlands.Aubert.General
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M)

/-- The actual product-induced coefficient space with the positive half-modulus
applied on the Levi before inflation. -/
abbrev leviProductInducedCoefficientObject : SmoothRep ℂ (G × G) :=
  (DynamicNormalization.leviTwistedInductionFunctor (h.prod h) (hU.prod hU)).obj
    (productLeviObject A A.contragredient)

/-- Contract an actual source-normalized function along `(k*g,k)`. -/
def leviProductInducedCoefficientIntegrand (g : G) :
    leviProductInducedCoefficientObject h hU A →ₗ[ℂ] ((⊤ : Subgroup G) → ℂ) where
  toFun F k :=
    TensorProduct.lift (smoothDualPairing A.representation).flip
      (Induction.eval (P.prod P)
        (leviInflatedInducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject A A.contragredient)) F ((k : G) * g, k))
  map_add' F J := by
    funext k
    exact map_add (TensorProduct.lift (smoothDualPairing A.representation).flip) _ _
  map_smul' c F := by
    funext k
    exact map_smul (TensorProduct.lift (smoothDualPairing A.representation).flip) c _

variable [SecondCountableTopology G] (huni : IsUnimodularModulus U hU)

/-- The value-preserving comparison of the two actual product coefficient
models. Quotient compactness is not needed for this comparison. -/
abbrev productInducedCoefficientLeviEquiv :
    Representation.Equiv
      (productInducedCoefficientObject h hU A).representation
      (leviProductInducedCoefficientObject h hU A).representation :=
  normalizedInductionLeviEquiv (h.prod h) (hU.prod hU)
    (isUnimodularModulus_prod hU hU huni huni) (productLeviObject A A.contragredient)

@[simp]
theorem productInducedCoefficientLeviEquiv_eval
    (F : productInducedCoefficientObject h hU A) (x : G × G) :
    Induction.eval (P.prod P)
        (leviInflatedInducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject A A.contragredient))
        (productInducedCoefficientLeviEquiv h hU A huni F) x =
      Induction.eval (P.prod P)
        (inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject A A.contragredient)) F x :=
  normalizedInductionLeviEquiv_eval (h.prod h) (hU.prod hU)
    (isUnimodularModulus_prod hU hU huni huni) (productLeviObject A A.contragredient) F x

/-- Both normalizations give the same diagonal contraction at every argument. -/
@[simp]
theorem leviProductInducedCoefficientIntegrand_compare
    (F : productInducedCoefficientObject h hU A) (g : G) :
    leviProductInducedCoefficientIntegrand h hU A g
        (productInducedCoefficientLeviEquiv h hU A huni F) =
      productInducedCoefficientIntegrand h hU A g F := by
  funext k
  exact congrArg (TensorProduct.lift (smoothDualPairing A.representation).flip)
    (normalizedInductionLeviEquiv_eval (h.prod h) (hU.prod hU)
      (isUnimodularModulus_prod hU hU huni huni) (productLeviObject A A.contragredient)
      F ((k : G) * g, k))

@[simp]
theorem leviProductInducedCoefficientIntegrand_compare_symm
    (F : leviProductInducedCoefficientObject h hU A) (g : G) :
    productInducedCoefficientIntegrand h hU A g
        ((productInducedCoefficientLeviEquiv h hU A huni).symm F) =
      leviProductInducedCoefficientIntegrand h hU A g F := by
  funext k
  exact congrArg (TensorProduct.lift (smoothDualPairing A.representation).flip)
    (normalizedInductionLeviEquiv_symm_eval (h.prod h) (hU.prod hU)
      (isUnimodularModulus_prod hU hU huni huni) (productLeviObject A A.contragredient)
      F ((k : G) * g, k))

section Integral

variable [CompactSpace (Induction.LeftQuotient P)]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace P]
  (hP : IsClosed (P : Set G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hmod : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))

include huni hmod in
/-- Integrability of the original diagonal contraction follows from the
published full-parabolic theorem and value preservation. -/
theorem leviProductInducedCoefficientIntegrand_integrable
    (F : leviProductInducedCoefficientObject h hU A) (g : G) :
    Integrable (leviProductInducedCoefficientIntegrand h hU A g F)
      (normalizedInductionBruhatMeasure hP hG) := by
  have hi := productInducedCoefficientIntegrand_integrable h hU A hP hG hmod
    ((productInducedCoefficientLeviEquiv h hU A huni).symm F) g
  exact (leviProductInducedCoefficientIntegrand_compare_symm h hU A huni F g) ▸ hi

variable (hm : Continuous h.projection) (hA : A.IsAdmissible)

/-- The existing coefficient map, transported to actual source-normalized
product functions by the inverse value-preserving comparison. -/
def leviProductInducedCoefficientMap :
    leviProductInducedCoefficientObject h hU A →ₗ[ℂ] LocallyConstant G ℂ :=
  (productInducedCoefficientMap h hU A hP hG hmod hm hA).comp
    (productInducedCoefficientLeviEquiv h hU A huni).symm.toLinearMap

/-- The coefficient map commutes with the actual normalization comparison. -/
@[simp]
theorem leviProductInducedCoefficientMap_compare
    (F : productInducedCoefficientObject h hU A) :
    leviProductInducedCoefficientMap h hU A huni hP hG hmod hm hA
        (productInducedCoefficientLeviEquiv h hU A huni F) =
      productInducedCoefficientMap h hU A hP hG hmod hm hA F := by
  change productInducedCoefficientMap h hU A hP hG hmod hm hA
    ((productInducedCoefficientLeviEquiv h hU A huni).symm
      (productInducedCoefficientLeviEquiv h hU A huni F)) = _
  rw [Representation.Equiv.symm_apply_apply]

/-- Every coefficient is the integral of its actual diagonal contraction,
independently of a tensor expansion. -/
theorem leviProductInducedCoefficientMap_integral
    (F : leviProductInducedCoefficientObject h hU A) (g : G) :
    leviProductInducedCoefficientMap h hU A huni hP hG hmod hm hA F g =
      ∫ k : (⊤ : Subgroup G), leviProductInducedCoefficientIntegrand h hU A g F k
        ∂normalizedInductionBruhatMeasure hP hG := by
  exact (productInducedCoefficientMap_integral h hU A hP hG hmod hm hA
    ((productInducedCoefficientLeviEquiv h hU A huni).symm F) g).trans
      (congrArg (fun φ : (⊤ : Subgroup G) → ℂ =>
        ∫ k, φ k ∂normalizedInductionBruhatMeasure hP hG)
        (leviProductInducedCoefficientIntegrand_compare_symm h hU A huni F g))

/-- On the canonical source-normalized tensor the coefficient is
`∫ k, fdual(k)(f(k*g))`, with the same fixed quotient-integration measure. -/
theorem leviProductInducedCoefficientMap_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (fdual : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) (g : G) :
    leviProductInducedCoefficientMap h hU A huni hP hG hmod hm hA
        (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
          (f ⊗ₜ[ℂ] fdual)) g =
      ∫ k : (⊤ : Subgroup G), smoothDualPairing A.representation
        (Induction.eval P (leviInflatedInducingRepresentation h hU A.contragredient) fdual k)
        (Induction.eval P (leviInflatedInducingRepresentation h hU A) f ((k : G) * g))
        ∂normalizedInductionBruhatMeasure hP hG := by
  apply Eq.trans (leviProductInducedCoefficientMap_integral h hU A huni hP hG hmod hm hA
    (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
      (f ⊗ₜ[ℂ] fdual)) g)
  apply integral_congr_ae
  filter_upwards [] with k
  exact congrArg (TensorProduct.lift (smoothDualPairing A.representation).flip)
    (leviNormalizedProductInductionTensorEquiv_tmul_eval h h hU hU huni huni
      A A.contragredient f fdual ((k : G) * g, k))

/-- The actual product action has the source's right and inverse-left
translation convention on every coefficient. -/
theorem leviProductInducedCoefficientMap_action
    (x : G × G) (F : leviProductInducedCoefficientObject h hU A) (g : G) :
    leviProductInducedCoefficientMap h hU A huni hP hG hmod hm hA
        ((leviProductInducedCoefficientObject h hU A).representation x F) g =
      leviProductInducedCoefficientMap h hU A huni hP hG hmod hm hA F
        (x.2⁻¹ * g * x.1) := by
  let E := productInducedCoefficientLeviEquiv h hU A huni
  have he : E.symm ((leviProductInducedCoefficientObject h hU A).representation x F) =
      (productInducedCoefficientObject h hU A).representation x (E.symm F) :=
    congrArg (fun T : leviProductInducedCoefficientObject h hU A →ₗ[ℂ]
      productInducedCoefficientObject h hU A => T F) (E.symm.isIntertwining' x)
  change productInducedCoefficientMap h hU A hP hG hmod hm hA
    (E.symm ((leviProductInducedCoefficientObject h hU A).representation x F)) g = _
  rw [he, productInducedCoefficientMap_action]
  rfl

/-- The image is the actual smooth coefficient space of normalized induction. -/
theorem range_leviProductInducedCoefficientMap :
    LinearMap.range (leviProductInducedCoefficientMap h hU A huni hP hG hmod hm hA) =
      LinearMap.range (normalizedCoefficientMap h hU A) := by
  have hr : LinearMap.range (leviProductInducedCoefficientMap h hU A huni hP hG hmod hm hA) =
      LinearMap.range (productInducedCoefficientMap h hU A hP hG hmod hm hA) := by
    apply le_antisymm
    · rintro f ⟨F, rfl⟩
      exact ⟨(productInducedCoefficientLeviEquiv h hU A huni).symm F, rfl⟩
    · rintro f ⟨F, rfl⟩
      refine ⟨productInducedCoefficientLeviEquiv h hU A huni F, ?_⟩
      exact leviProductInducedCoefficientMap_compare h hU A huni hP hG hmod hm hA F
  exact hr.trans (range_productInducedCoefficientMap h hU A hP hG hmod hm hA)

end Integral

end Langlands.Plancherel
