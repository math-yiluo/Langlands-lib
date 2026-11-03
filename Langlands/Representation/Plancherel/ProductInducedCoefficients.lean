import Langlands.Representation.Plancherel.NormalizedProductInduction
import Langlands.Representation.Plancherel.NormalizedInductionDualTensor

/-!
# Coefficients on the actual normalized product induction

Compose the proved product-induction comparison with integral duality, and
retain the diagonal integral formula on the actual induced function space.
-/

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

/-- Waldspurger's product-induced coefficient space, using the actual product
parabolic, product Levi and canonical Haar-normalized induction. -/
def productInducedCoefficientObject : SmoothRep ℂ (G × G) :=
  (normalizedInductionFunctor (h.prod h) (hU.prod hU)).obj
    (productLeviObject A A.contragredient)

/-- Contract the value of an actual product-induced function at `(k*g,k)`.
This is linear in the induced function and uses the smooth bilinear pairing. -/
def productInducedCoefficientIntegrand (g : G) :
    productInducedCoefficientObject h hU A →ₗ[ℂ] ((⊤ : Subgroup G) → ℂ) where
  toFun F k :=
    TensorProduct.lift (smoothDualPairing A.representation).flip
      (Induction.eval (P.prod P)
        (inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject A A.contragredient)) F ((k : G) * g, k))
  map_add' F J := by
    funext k
    exact map_add (TensorProduct.lift (smoothDualPairing A.representation).flip) _ _
  map_smul' c F := by
    funext k
    exact map_smul (TensorProduct.lift (smoothDualPairing A.representation).flip) c _

section ProductComparison

variable [SecondCountableTopology G] [CompactSpace (Induction.LeftQuotient P)]

/-- The diagonal contraction on a pure tensor is the usual coefficient
integrand, with right translation of the vector factor. -/
@[simp]
theorem productInducedCoefficientIntegrand_tensor
    (f : (normalizedInductionFunctor h hU).obj A)
    (fdual : (normalizedInductionFunctor h hU).obj A.contragredient)
    (g : G) (k : (⊤ : Subgroup G)) :
    productInducedCoefficientIntegrand h hU A g
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
          (f ⊗ₜ[ℂ] fdual)) k =
      smoothDualPairing A.representation
        (Induction.eval P (inducingRepresentation h hU A.contragredient) fdual k)
        (Induction.eval P (inducingRepresentation h hU A) f ((k : G) * g)) := by
  exact congrArg (TensorProduct.lift (smoothDualPairing A.representation).flip)
    (normalizedProductInductionTensorEquiv_tmul_eval h h hU hU A A.contragredient
      f fdual ((k : G) * g, k))

variable [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (hP : IsClosed (P : Set G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))

include hδ in
/-- The diagonal contraction is genuinely integrable for every vector of the
actual product induction. Inducing admissibility is not required. -/
theorem productInducedCoefficientIntegrand_integrable
    (F : productInducedCoefficientObject h hU A) (g : G) :
    Integrable (productInducedCoefficientIntegrand h hU A g F)
      (normalizedInductionBruhatMeasure hP hG) := by
  obtain ⟨t, rfl⟩ :=
    (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).surjective F
  induction t using TensorProduct.inductionOn with
  | tmul f fdual =>
    have he : productInducedCoefficientIntegrand h hU A g
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
          (f ⊗ₜ[ℂ] fdual)) =
        fun k : (⊤ : Subgroup G) => smoothDualPairing A.representation
          (Induction.eval P (inducingRepresentation h hU A.contragredient) fdual k)
          (Induction.eval P (inducingRepresentation h hU A) f ((k : G) * g)) :=
      funext (productInducedCoefficientIntegrand_tensor h hU A f fdual g)
    exact he.symm ▸
      normalizedInductionCoefficient_integrable h hU hP hG hδ A fdual f g
  | add t s ht hs =>
    let E := normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
    let J := productInducedCoefficientIntegrand h hU A g
    have he : J (E (t + s)) = J (E t) + J (E s) :=
      (congrArg J (map_add E t s)).trans (map_add J (E t) (E s))
    exact he.symm ▸ ht.add hs

variable (hm : Continuous h.projection) (hA : A.IsAdmissible)

set_option maxHeartbeats 800000 in
/-- Identify actual normalized product induction with the coefficient tensor
by the inverse product comparison followed by the proved integral duality. -/
def productInducedCoefficientTensorEquiv :
    Representation.Equiv
      (productInducedCoefficientObject h hU A).representation
      (coefficientTensorAction ((normalizedInductionFunctor h hU).obj A)) :=
  (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm.trans
    (normalizedInductionDualTensorEquiv h hU hP hm hG hδ A hA)

/-- The comparison cancels the product-induction map before applying duality. -/
@[simp]
theorem productInducedCoefficientTensorEquiv_tensor
    (t : NormalizedInductionDualTensor h hU A) :
    productInducedCoefficientTensorEquiv h hU A hP hG hδ hm hA
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient t) =
      normalizedInductionDualTensorEquiv h hU hP hm hG hδ A hA t := by
  change normalizedInductionDualTensorEquiv h hU hP hm hG hδ A hA
    ((normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient t)) = _
  rw [Representation.Equiv.symm_apply_apply]

/-- The actual coefficient map on normalized induction from `P × P`. -/
def productInducedCoefficientMap :
    productInducedCoefficientObject h hU A →ₗ[ℂ] LocallyConstant G ℂ :=
  (normalizedCoefficientMap h hU A).comp
    (productInducedCoefficientTensorEquiv h hU A hP hG hδ hm hA).toLinearMap

/-- On the tensor of the two normalized inductions, the actual product-induced
coefficient map is the previously constructed integral coefficient map. -/
theorem productInducedCoefficientMap_tensor
    (t : NormalizedInductionDualTensor h hU A) :
    productInducedCoefficientMap h hU A hP hG hδ hm hA
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient t) =
      normalizedInductionDualCoefficientMap h hU hP hm hG hδ A hA t := by
  change normalizedCoefficientMap h hU A
    (productInducedCoefficientTensorEquiv h hU A hP hG hδ hm hA
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient t)) = _
  rw [productInducedCoefficientTensorEquiv_tensor]
  rfl

/-- The canonical pointwise pure tensor has coefficient
`∫ k, fdual(k)(f(k*g))`, against the fixed quotient-integration measure. -/
theorem productInducedCoefficientMap_tmul
    (f : (normalizedInductionFunctor h hU).obj A)
    (fdual : (normalizedInductionFunctor h hU).obj A.contragredient) (g : G) :
    productInducedCoefficientMap h hU A hP hG hδ hm hA
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
          (f ⊗ₜ[ℂ] fdual)) g =
      ∫ k : (⊤ : Subgroup G), smoothDualPairing A.representation
        (Induction.eval P (inducingRepresentation h hU A.contragredient) fdual k)
        (Induction.eval P (inducingRepresentation h hU A) f ((k : G) * g))
        ∂normalizedInductionBruhatMeasure hP hG := by
  rw [productInducedCoefficientMap_tensor]
  exact normalizedInductionDualCoefficientMap_tmul h hU hP hm hG hδ A hA f fdual g

set_option maxRecDepth 2048 in
/-- Every actual product-induced coefficient is the integral of its diagonal
contraction; this formula does not depend on choosing a tensor expansion. -/
theorem productInducedCoefficientMap_integral
    (F : productInducedCoefficientObject h hU A) (g : G) :
    productInducedCoefficientMap h hU A hP hG hδ hm hA F g =
      ∫ k : (⊤ : Subgroup G), productInducedCoefficientIntegrand h hU A g F k
        ∂normalizedInductionBruhatMeasure hP hG := by
  obtain ⟨t, rfl⟩ :=
    (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).surjective F
  induction t using TensorProduct.inductionOn with
  | tmul f fdual =>
    have he : productInducedCoefficientIntegrand h hU A g
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
          (f ⊗ₜ[ℂ] fdual)) =
        fun k : (⊤ : Subgroup G) => smoothDualPairing A.representation
          (Induction.eval P (inducingRepresentation h hU A.contragredient) fdual k)
          (Induction.eval P (inducingRepresentation h hU A) f ((k : G) * g)) :=
      funext (productInducedCoefficientIntegrand_tensor h hU A f fdual g)
    exact (productInducedCoefficientMap_tmul h hU A hP hG hδ hm hA f fdual g).trans
      (congrArg (fun φ : (⊤ : Subgroup G) → ℂ =>
        ∫ k, φ k ∂normalizedInductionBruhatMeasure hP hG) he.symm)
  | add t s ht hs =>
    let E := normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
    let B := productInducedCoefficientMap h hU A hP hG hδ hm hA
    let J := productInducedCoefficientIntegrand h hU A g
    have hcoef : B (E (t + s)) g = B (E t) g + B (E s) g :=
      (congrArg (fun v => B v g) (map_add E t s)).trans
        (congrArg (fun q : LocallyConstant G ℂ => q g) (map_add B (E t) (E s)))
    have hfun : J (E (t + s)) = J (E t) + J (E s) :=
      (congrArg J (map_add E t s)).trans (map_add J (E t) (E s))
    calc
      B (E (t + s)) g = B (E t) g + B (E s) g := hcoef
      _ = (∫ k, J (E t) k ∂normalizedInductionBruhatMeasure hP hG) +
          ∫ k, J (E s) k ∂normalizedInductionBruhatMeasure hP hG :=
        congrArg₂ (· + ·) ht hs
      _ = ∫ k, (J (E t) + J (E s)) k
          ∂normalizedInductionBruhatMeasure hP hG :=
        (integral_add
          (productInducedCoefficientIntegrand_integrable h hU A hP hG hδ (E t) g)
          (productInducedCoefficientIntegrand_integrable h hU A hP hG hδ (E s) g)).symm
      _ = ∫ k, J (E (t + s)) k ∂normalizedInductionBruhatMeasure hP hG :=
        congrArg (fun φ : (⊤ : Subgroup G) → ℂ =>
          ∫ k, φ k ∂normalizedInductionBruhatMeasure hP hG) hfun.symm

/-- The actual product action becomes right and inverse-left translation on
every coefficient, with the multiplication order of Waldspurger's convention. -/
theorem productInducedCoefficientMap_action
    (x : G × G) (F : productInducedCoefficientObject h hU A) (g : G) :
    productInducedCoefficientMap h hU A hP hG hδ hm hA
        ((productInducedCoefficientObject h hU A).representation x F) g =
      productInducedCoefficientMap h hU A hP hG hδ hm hA F (x.2⁻¹ * g * x.1) := by
  let E := productInducedCoefficientTensorEquiv h hU A hP hG hδ hm hA
  have he : E ((productInducedCoefficientObject h hU A).representation x F) =
      coefficientTensorAction ((normalizedInductionFunctor h hU).obj A) x (E F) :=
    congrArg (fun T : productInducedCoefficientObject h hU A →ₗ[ℂ]
      NormalizedCoefficientTensor h hU A => T F) (E.isIntertwining' x)
  change coefficientTensorMap _
    (E ((productInducedCoefficientObject h hU A).representation x F)) g = _
  rw [he, coefficientTensorMap_action]
  rfl

/-- Every product-induced coefficient has one common open subgroup of left
and right invariance. -/
theorem productInducedCoefficientMap_biInvariant
    (F : productInducedCoefficientObject h hU A) :
    ∃ K : OpenSubgroup G, ∀ (k l : K) (g : G),
      productInducedCoefficientMap h hU A hP hG hδ hm hA F
          ((k : G) * g * (l : G)) =
        productInducedCoefficientMap h hU A hP hG hδ hm hA F g :=
  normalizedCoefficientMap_biInvariant h hU A
    (productInducedCoefficientTensorEquiv h hU A hP hG hδ hm hA F)

/-- The image is the actual smooth coefficient space of normalized induction,
expressed as the range of the canonical coefficient-tensor map. -/
theorem range_productInducedCoefficientMap :
    LinearMap.range (productInducedCoefficientMap h hU A hP hG hδ hm hA) =
      LinearMap.range (normalizedCoefficientMap h hU A) := by
  let E := productInducedCoefficientTensorEquiv h hU A hP hG hδ hm hA
  apply le_antisymm
  · rintro f ⟨F, rfl⟩
    exact ⟨E F, rfl⟩
  · rintro f ⟨t, rfl⟩
    refine ⟨E.symm t, ?_⟩
    change normalizedCoefficientMap h hU A (E (E.symm t)) = _
    rw [E.apply_symm_apply]

end ProductComparison

end Langlands.Plancherel
