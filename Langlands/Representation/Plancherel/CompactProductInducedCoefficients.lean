import Langlands.Representation.Plancherel.CompactNormalizedInductionDuality
import Langlands.Representation.Plancherel.ProductInducedCoefficients

/-! # Compact probability coefficients on actual product induction -/

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

/-- The existing actual diagonal contraction, restricted to the supplied K. -/
def integrand (g : G) :
    productInducedCoefficientObject h hU A →ₗ[ℂ] (K → ℂ) where
  toFun F k := productInducedCoefficientIntegrand h hU A g F ⟨k, Subgroup.mem_top _⟩
  map_add' F J := by
    funext k
    exact congrFun (map_add (productInducedCoefficientIntegrand h hU A g) F J) _
  map_smul' c F := by
    funext k
    exact congrFun (map_smul (productInducedCoefficientIntegrand h hU A g) c F) _

/-- The diagonal scalar contraction of every actual induced vector is locally
constant on K, without admissibility or modulus hypotheses. -/
theorem integrand_isLocallyConstant
    (F : productInducedCoefficientObject h hU A) (g : G) :
    IsLocallyConstant (integrand h hU A K g F) := by
  exact ((Induction.eval_isLocallyConstant (P.prod P)
    (inducingRepresentation (h.prod h) (hU.prod hU)
      (productLeviObject A A.contragredient)) F).comp
        (TensorProduct.lift (smoothDualPairing A.representation).flip)).comp_continuous
    ((continuous_subtype_val.mul continuous_const).prodMk continuous_subtype_val)

variable [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] (hK : IsCompact (K : Set G))

omit [SecondCountableTopology G] [T2Space G] in
/-- Every diagonal contraction is integrable for the fixed K Haar probability.
This follows from compactness and local constancy on the actual carrier. -/
theorem integrand_integrable
    (F : productInducedCoefficientObject h hU A) (g : G) :
    Integrable (integrand h hU A K g F) (measure K hK) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact (integrand_isLocallyConstant h hU A K F g).continuous
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable [LocallyCompactSpace P]
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (hA : A.IsAdmissible)

/-- Tensor the identity with inverse compact probability duality. -/
def dualTensorEquiv :
    Representation.Equiv (normalizedInductionDualTensorAction h hU A)
      (coefficientTensorAction ((normalizedInductionFunctor h hU).obj A)) :=
  Representation.Equiv.mk
    (TensorProduct.congr (LinearEquiv.refl ℂ _)
      (integralDualEquiv h hU hP hm K hK hPK hG hδ A hA).symm.toLinearEquiv)
    (by
      intro x
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul f fdual =>
        let E := integralDualEquiv h hU hP hm K hK hPK hG hδ A hA
        have he : E.symm
              (((normalizedInductionFunctor h hU).obj A.contragredient).representation
                x.2 fdual) =
            ((normalizedInductionFunctor h hU).obj A).contragredient.representation
              x.2 (E.symm fdual) :=
          congrArg (fun T :
            ((normalizedInductionFunctor h hU).obj A.contragredient) →ₗ[ℂ]
              ((normalizedInductionFunctor h hU).obj A).contragredient => T fdual)
            (E.symm.isIntertwining' x.2)
        exact congrArg (fun ℓ : ((normalizedInductionFunctor h hU).obj A).contragredient =>
          ((normalizedInductionFunctor h hU).obj A).representation x.1 f ⊗ₜ[ℂ] ℓ) he
      | add t s ht hs => simp only [LinearMap.comp_apply, map_add, ht, hs])

set_option maxHeartbeats 800000 in
/-- The actual product induction is identified with coefficient tensors by
inverse product comparison followed by the constructed compact duality. -/
def coefficientTensorEquiv :
    Representation.Equiv
      (productInducedCoefficientObject h hU A).representation
      (coefficientTensorAction ((normalizedInductionFunctor h hU).obj A)) := by
  letI : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK hPK
  exact (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm.trans
    (dualTensorEquiv h hU A K hK hP hm hPK hG hδ hA)

/-- The probability-normalized coefficient map on the original product-induced
function carrier. -/
def coefficientMap :
    productInducedCoefficientObject h hU A →ₗ[ℂ] LocallyConstant G ℂ :=
  (normalizedCoefficientMap h hU A).comp
    (coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hA).toLinearMap

section TensorFormula

variable [CompactSpace (Induction.LeftQuotient P)]

/-- On pure tensors, evaluation gives the compact integral of the paired
induced functions. The vector factor is translated on the right. -/
theorem coefficientMap_tmul
    (f : (normalizedInductionFunctor h hU).obj A)
    (fdual : (normalizedInductionFunctor h hU).obj A.contragredient) (g : G) :
    coefficientMap h hU A K hK hP hm hPK hG hδ hA
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
          (f ⊗ₜ[ℂ] fdual)) g =
      ∫ k : K, smoothDualPairing A.representation
        (Induction.eval P (inducingRepresentation h hU A.contragredient) fdual k)
        (Induction.eval P (inducingRepresentation h hU A) f ((k : G) * g))
        ∂measure K hK := by
  change normalizedCoefficientMap h hU A
    (dualTensorEquiv h hU A K hK hP hm hPK hG hδ hA
      ((normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
          (f ⊗ₜ[ℂ] fdual)))) g = _
  rw [Representation.Equiv.symm_apply_apply]
  change smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation
    ((integralDualEquiv h hU hP hm K hK hPK hG hδ A hA).symm fdual)
    (((normalizedInductionFunctor h hU).obj A).representation g f) = _
  rw [integralDualEquiv_pairing h hU hP hm K hK hPK hG hδ A hA,
    Representation.Equiv.apply_symm_apply]
  rfl

end TensorFormula

set_option maxRecDepth 2048 in
/-- Every actual product-induced coefficient equals the integral of its
original diagonal contraction against K Haar probability. -/
theorem coefficientMap_integral
    (F : productInducedCoefficientObject h hU A) (g : G) :
    coefficientMap h hU A K hK hP hm hPK hG hδ hA F g =
      ∫ k : K, integrand h hU A K g F k ∂measure K hK := by
  let : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK hPK
  obtain ⟨t, rfl⟩ :=
    (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).surjective F
  induction t using TensorProduct.inductionOn with
  | tmul f fdual =>
    have he : integrand h hU A K g
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
          (f ⊗ₜ[ℂ] fdual)) =
        fun k : K => smoothDualPairing A.representation
          (Induction.eval P (inducingRepresentation h hU A.contragredient) fdual k)
          (Induction.eval P (inducingRepresentation h hU A) f ((k : G) * g)) := by
      funext k
      exact productInducedCoefficientIntegrand_tensor h hU A f fdual g
        ⟨k, Subgroup.mem_top _⟩
    exact (coefficientMap_tmul h hU A K hK hP hm hPK hG hδ hA f fdual g).trans
      (congrArg (fun φ : K → ℂ => ∫ k, φ k ∂measure K hK) he.symm)
  | add t s ht hs =>
    let E := normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
    let B := coefficientMap h hU A K hK hP hm hPK hG hδ hA
    let J := integrand h hU A K g
    have hcoef : B (E (t + s)) g = B (E t) g + B (E s) g :=
      (congrArg (fun v => B v g) (map_add E t s)).trans
        (congrArg (fun q : LocallyConstant G ℂ => q g) (map_add B (E t) (E s)))
    have hfun : J (E (t + s)) = J (E t) + J (E s) :=
      (congrArg J (map_add E t s)).trans (map_add J (E t) (E s))
    calc
      B (E (t + s)) g = B (E t) g + B (E s) g := hcoef
      _ = (∫ k, J (E t) k ∂measure K hK) + ∫ k, J (E s) k ∂measure K hK :=
        congrArg₂ (· + ·) ht hs
      _ = ∫ k, (J (E t) + J (E s)) k ∂measure K hK :=
        (integral_add (integrand_integrable h hU A K hK (E t) g)
          (integrand_integrable h hU A K hK (E s) g)).symm
      _ = ∫ k, J (E (t + s)) k ∂measure K hK :=
        congrArg (fun φ : K → ℂ => ∫ k, φ k ∂measure K hK) hfun.symm

/-- The actual product action has the canonical coefficient translation law. -/
theorem coefficientMap_action
    (x : G × G) (F : productInducedCoefficientObject h hU A) (g : G) :
    coefficientMap h hU A K hK hP hm hPK hG hδ hA
        ((productInducedCoefficientObject h hU A).representation x F) g =
      coefficientMap h hU A K hK hP hm hPK hG hδ hA F (x.2⁻¹ * g * x.1) := by
  let E := coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hA
  have he : E ((productInducedCoefficientObject h hU A).representation x F) =
      coefficientTensorAction ((normalizedInductionFunctor h hU).obj A) x (E F) :=
    congrArg (fun T : productInducedCoefficientObject h hU A →ₗ[ℂ]
      NormalizedCoefficientTensor h hU A => T F) (E.isIntertwining' x)
  change coefficientTensorMap _
    (E ((productInducedCoefficientObject h hU A).representation x F)) g = _
  rw [he, coefficientTensorMap_action]
  rfl

/-- Every resulting coefficient is invariant under left and right translation
by one open subgroup. -/
theorem coefficientMap_biInvariant
    (F : productInducedCoefficientObject h hU A) :
    ∃ L : OpenSubgroup G, ∀ (k l : L) (g : G),
      coefficientMap h hU A K hK hP hm hPK hG hδ hA F
          ((k : G) * g * (l : G)) =
        coefficientMap h hU A K hK hP hm hPK hG hδ hA F g :=
  normalizedCoefficientMap_biInvariant h hU A
    (coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hA F)

/-- The image is exactly the actual coefficient space of normalized induction. -/
theorem range_coefficientMap :
    LinearMap.range (coefficientMap h hU A K hK hP hm hPK hG hδ hA) =
      LinearMap.range (normalizedCoefficientMap h hU A) := by
  let E := coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hA
  apply le_antisymm
  · rintro f ⟨F, rfl⟩
    exact ⟨E F, rfl⟩
  · rintro f ⟨t, rfl⟩
    refine ⟨E.symm t, ?_⟩
    change normalizedCoefficientMap h hU A (E (E.symm t)) = _
    rw [E.apply_symm_apply]

end Langlands.Plancherel.CompactInduction
