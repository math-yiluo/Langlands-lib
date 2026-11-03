import Langlands.Representation.Plancherel.NormalizedCoefficientTensors
import Langlands.Representation.Aubert.General.RationalInductionDualityAssembly

/-!
# Integral comparison for normalized induced coefficient tensors

The same-parabolic smooth-dual comparison of Waldspurger I.3, and its tensor
consequence used in V.1. The measure is constructed from the compact-quotient
Bruhat-function theorem; the comparison is not an assumed duality.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G}

section Measure

variable [LocallyCompactSpace P] [CompactSpace (Induction.LeftQuotient P)]

/-- One Bruhat-density measure, fixed before the inducing representation is
chosen. It represents integration of modular-covariant functions on `P \ G`. -/
def normalizedInductionBruhatMeasure (hP : IsClosed (P : Set G))
    (hG : ∀ g : G, Measure.modularCharacter g = 1) :
    Measure (⊤ : Subgroup G) :=
  Classical.choose (Induction.exists_compactQuotient_measure hG P hP)

/-- Positivity and the scalar quotient-integration law of the chosen measure. -/
theorem normalizedInductionBruhatMeasure_spec (hP : IsClosed (P : Set G))
    (hG : ∀ g : G, Measure.modularCharacter g = 1) :
    (∀ W : Set (⊤ : Subgroup G), IsOpen W →
      (1 : (⊤ : Subgroup G)) ∈ W → 0 < normalizedInductionBruhatMeasure hP hG W) ∧
    ∀ φ : G → ℂ, IsLocallyConstant φ →
      (∀ (q : P) (x : G), φ ((q : G) * x) =
        ((Measure.modularCharacter q : ℝ) : ℂ) * φ x) →
      ∀ g : G, Integrable (fun k : (⊤ : Subgroup G) => φ ((k : G) * g))
          (normalizedInductionBruhatMeasure hP hG) ∧
        (∫ k : (⊤ : Subgroup G), φ ((k : G) * g)
          ∂normalizedInductionBruhatMeasure hP hG) =
        ∫ k : (⊤ : Subgroup G), φ (k : G)
          ∂normalizedInductionBruhatMeasure hP hG :=
  Classical.choose_spec (Induction.exists_compactQuotient_measure hG P hP)

end Measure

section Tensor

/-- The two actual normalized inductions, before identifying the second factor
with the smooth dual of the first. -/
abbrev NormalizedInductionDualTensor (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) :=
  ((normalizedInductionFunctor h hU).obj A) ⊗[ℂ]
    ((normalizedInductionFunctor h hU).obj A.contragredient)

/-- Each coordinate acts by right translation in its induced factor. -/
def normalizedInductionDualTensorAction (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation ℂ (G × G) (NormalizedInductionDualTensor h hU A) :=
  Representation.tprod
    (((normalizedInductionFunctor h hU).obj A).representation.comp (MonoidHom.fst G G))
    (((normalizedInductionFunctor h hU).obj A.contragredient).representation.comp
      (MonoidHom.snd G G))

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
@[simp]
theorem normalizedInductionDualTensorAction_tmul
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ M) (x : G × G)
    (f : (normalizedInductionFunctor h hU).obj A)
    (fdual : (normalizedInductionFunctor h hU).obj A.contragredient) :
    normalizedInductionDualTensorAction h hU A x (f ⊗ₜ[ℂ] fdual) =
      ((normalizedInductionFunctor h hU).obj A).representation x.1 f ⊗ₜ[ℂ]
        ((normalizedInductionFunctor h hU).obj A.contragredient).representation x.2 fdual :=
  rfl

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The external action on the two induced factors is smooth. -/
theorem isSmooth_normalizedInductionDualTensorAction
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    IsSmooth (normalizedInductionDualTensorAction h hU A) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul f fdual =>
    obtain ⟨K, hK⟩ := ((normalizedInductionFunctor h hU).obj A).isSmooth f
    obtain ⟨L, hL⟩ :=
      ((normalizedInductionFunctor h hU).obj A.contragredient).isSmooth fdual
    refine ⟨K.prod L, ?_⟩
    intro x
    change ((normalizedInductionFunctor h hU).obj A).representation
        (x : G × G).1 f ⊗ₜ[ℂ]
      ((normalizedInductionFunctor h hU).obj A.contragredient).representation
        (x : G × G).2 fdual = f ⊗ₜ[ℂ] fdual
    have hf : ((normalizedInductionFunctor h hU).obj A).representation
        (x : G × G).1 f = f := hK ⟨_, x.property.1⟩
    have hdual : ((normalizedInductionFunctor h hU).obj A.contragredient).representation
        (x : G × G).2 fdual = fdual := hL ⟨_, x.property.2⟩
    rw [hf, hdual]
  | add t s ht hs => exact isSmoothVector_add ht hs

end Tensor

section Duality

variable (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  [LocallyCompactSpace P] [CompactSpace (Induction.LeftQuotient P)]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))

include hm hδ in
/-- The actual same-parabolic dual equivalence, with its integral normalization,
exists for every admissible inducing object. -/
theorem exists_normalizedInductionIntegralDualEquiv
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) :
    ∃ E : Representation.Equiv
        ((normalizedInductionFunctor h hU).obj A).contragredient.representation
        ((normalizedInductionFunctor h hU).obj A.contragredient).representation,
      ∀ (ℓ : ((normalizedInductionFunctor h hU).obj A).contragredient)
        (f : (normalizedInductionFunctor h hU).obj A),
        smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation ℓ f =
          ∫ k : (⊤ : Subgroup G), smoothDualPairing A.representation
            (Induction.eval P (inducingRepresentation h hU A.contragredient) (E ℓ) k)
            (Induction.eval P (inducingRepresentation h hU A) f k)
            ∂normalizedInductionBruhatMeasure hP hG := by
  obtain ⟨hpos, hscalar⟩ := normalizedInductionBruhatMeasure_spec hP hG
  have hsq : ∀ q : P,
      ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) *
        HaarModulus.closedHalfCharacter U hU P h.le_normalizer q =
      (((Measure.modularCharacter q : ℝ≥0) : ℝ) : ℂ) := by
    intro q
    rw [closedHalfCharacter_mul_self h hU q, hδ q]
  obtain ⟨E, hE⟩ := Induction.exists_integralDualEquiv_of_pos P h.projection
    (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
    (fun q => Measure.modularCharacter q) ⊤ (normalizedInductionBruhatMeasure hP hG)
    hm (HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer)
    hsq (compactOpenCofinal_of_isClosed (h.isClosed_levi hP hm)) hpos hscalar
    A.representation A.isSmooth
    (smoothInduced_inducingRepresentation_isAdmissible h hU hm A hA)
  exact exists_functorEquiv_of_twistEquiv h hU ⊤
    (normalizedInductionBruhatMeasure hP hG) A E hE

/-- Choose the equivalence furnished by the proved compact-quotient duality. -/
def normalizedInductionIntegralDualEquiv
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) :
    Representation.Equiv
      ((normalizedInductionFunctor h hU).obj A).contragredient.representation
      ((normalizedInductionFunctor h hU).obj A.contragredient).representation :=
  Classical.choose
    (exists_normalizedInductionIntegralDualEquiv h hU hP hm hG hδ A hA)

/-- Evaluation of the chosen dual equivalence is the actual bilinear integral. -/
theorem normalizedInductionIntegralDualEquiv_pairing
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible)
    (ℓ : ((normalizedInductionFunctor h hU).obj A).contragredient)
    (f : (normalizedInductionFunctor h hU).obj A) :
    smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation ℓ f =
      ∫ k : (⊤ : Subgroup G), smoothDualPairing A.representation
        (Induction.eval P (inducingRepresentation h hU A.contragredient)
          (normalizedInductionIntegralDualEquiv h hU hP hm hG hδ A hA ℓ) k)
        (Induction.eval P (inducingRepresentation h hU A) f k)
        ∂normalizedInductionBruhatMeasure hP hG :=
  Classical.choose_spec
    (exists_normalizedInductionIntegralDualEquiv h hU hP hm hG hδ A hA) ℓ f

include hδ in
/-- The integral pairing of two normalized induced functions is integrable.
No admissibility is needed for this assertion. -/
theorem normalizedInductionPairing_integrable
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (fdual : (normalizedInductionFunctor h hU).obj A.contragredient)
    (f : (normalizedInductionFunctor h hU).obj A) :
    Integrable (fun k : (⊤ : Subgroup G) => smoothDualPairing A.representation
      (Induction.eval P (inducingRepresentation h hU A.contragredient) fdual k)
      (Induction.eval P (inducingRepresentation h hU A) f k))
      (normalizedInductionBruhatMeasure hP hG) := by
  let χ := HaarModulus.closedHalfCharacter U hU P h.le_normalizer
  let τ := Langlands.twist χ (A.representation.comp h.projection)
  let υ := Langlands.twist χ ((smoothContragredient A.representation).comp h.projection)
  let e0 : ((normalizedInductionFunctor h hU).obj A).representation.Equiv
      (Induction.smoothInduced P τ) := Representation.Equiv.refl _
  let e2 : ((normalizedInductionFunctor h hU).obj A.contragredient).representation.Equiv
      (Induction.smoothInduced P υ) := Representation.Equiv.refl _
  have hsq : ∀ q : P, (χ q : ℂ) * χ q = ((Measure.modularCharacter q : ℝ) : ℂ) := by
    intro q
    rw [closedHalfCharacter_mul_self h hU q, hδ]
  have hi := (normalizedInductionBruhatMeasure_spec hP hG).2 _
    (Induction.bilinearPairing_isLocallyConstant P τ υ
      (smoothDualPairing A.representation) (e2 fdual) (e0 f))
    (by intro q x; rw [Induction.dualPairing_covariant P h.projection χ, hsq]) 1
  have hir : Integrable (fun k : (⊤ : Subgroup G) => smoothDualPairing A.representation
      (Induction.eval P υ (e2 fdual) k) (Induction.eval P τ (e0 f) k))
      (normalizedInductionBruhatMeasure hP hG) := by
    simpa only [mul_one] using hi.1
  exact hir

include hδ in
/-- The coefficient integrand with right translation of the vector factor
is genuinely integrable. -/
theorem normalizedInductionCoefficient_integrable
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (fdual : (normalizedInductionFunctor h hU).obj A.contragredient)
    (f : (normalizedInductionFunctor h hU).obj A) (g : G) :
    Integrable (fun k : (⊤ : Subgroup G) => smoothDualPairing A.representation
      (Induction.eval P (inducingRepresentation h hU A.contragredient) fdual k)
      (Induction.eval P (inducingRepresentation h hU A) f ((k : G) * g)))
      (normalizedInductionBruhatMeasure hP hG) :=
  normalizedInductionPairing_integrable h hU hP hG hδ A fdual
    (((normalizedInductionFunctor h hU).obj A).representation g f)

/-- Tensor the identity with the inverse of the proved integral duality.
This is an equivalence of the actual external product representations. -/
def normalizedInductionDualTensorEquiv
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) :
    Representation.Equiv (normalizedInductionDualTensorAction h hU A)
      (coefficientTensorAction ((normalizedInductionFunctor h hU).obj A)) :=
  Representation.Equiv.mk
    (TensorProduct.congr (LinearEquiv.refl ℂ _)
      (normalizedInductionIntegralDualEquiv h hU hP hm hG hδ A hA).symm.toLinearEquiv)
    (by
      intro x
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul f fdual =>
        let E := normalizedInductionIntegralDualEquiv h hU hP hm hG hδ A hA
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

@[simp]
theorem normalizedInductionDualTensorEquiv_tmul
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible)
    (f : (normalizedInductionFunctor h hU).obj A)
    (fdual : (normalizedInductionFunctor h hU).obj A.contragredient) :
    normalizedInductionDualTensorEquiv h hU hP hm hG hδ A hA (f ⊗ₜ[ℂ] fdual) =
      f ⊗ₜ[ℂ] (normalizedInductionIntegralDualEquiv h hU hP hm hG hδ A hA).symm fdual :=
  rfl

/-- The actual coefficient map on the tensor of the two normalized inductions. -/
def normalizedInductionDualCoefficientMap
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) :
    NormalizedInductionDualTensor h hU A →ₗ[ℂ] LocallyConstant G ℂ :=
  (normalizedCoefficientMap h hU A).comp
    (normalizedInductionDualTensorEquiv h hU hP hm hG hδ A hA).toLinearMap

/-- The pure-tensor coefficient is the quotient integral of
`fdual(k)(f(k*g))`, with the measure fixed independently of `A`. -/
theorem normalizedInductionDualCoefficientMap_tmul
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible)
    (f : (normalizedInductionFunctor h hU).obj A)
    (fdual : (normalizedInductionFunctor h hU).obj A.contragredient) (g : G) :
    normalizedInductionDualCoefficientMap h hU hP hm hG hδ A hA (f ⊗ₜ[ℂ] fdual) g =
      ∫ k : (⊤ : Subgroup G), smoothDualPairing A.representation
        (Induction.eval P (inducingRepresentation h hU A.contragredient) fdual k)
        (Induction.eval P (inducingRepresentation h hU A) f ((k : G) * g))
        ∂normalizedInductionBruhatMeasure hP hG := by
  change smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation
      ((normalizedInductionIntegralDualEquiv h hU hP hm hG hδ A hA).symm fdual)
      (((normalizedInductionFunctor h hU).obj A).representation g f) = _
  rw [normalizedInductionIntegralDualEquiv_pairing h hU hP hm hG hδ A hA,
    Representation.Equiv.apply_symm_apply]
  rfl

/-- The full tensor coefficient map has the same right and inverse-left
translation law as the canonical coefficient map. -/
theorem normalizedInductionDualCoefficientMap_action
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible)
    (x : G × G) (t : NormalizedInductionDualTensor h hU A) (g : G) :
    normalizedInductionDualCoefficientMap h hU hP hm hG hδ A hA
        (normalizedInductionDualTensorAction h hU A x t) g =
      normalizedInductionDualCoefficientMap h hU hP hm hG hδ A hA t
        (x.2⁻¹ * g * x.1) := by
  change coefficientTensorMap _
    ((normalizedInductionDualTensorEquiv h hU hP hm hG hδ A hA)
      (normalizedInductionDualTensorAction h hU A x t)) g = _
  let E := normalizedInductionDualTensorEquiv h hU hP hm hG hδ A hA
  have he : E (normalizedInductionDualTensorAction h hU A x t) =
      coefficientTensorAction ((normalizedInductionFunctor h hU).obj A) x (E t) :=
    congrArg (fun T : NormalizedInductionDualTensor h hU A →ₗ[ℂ]
      NormalizedCoefficientTensor h hU A => T t) (E.isIntertwining' x)
  calc
    coefficientTensorMap _ (E (normalizedInductionDualTensorAction h hU A x t)) g =
        coefficientTensorMap _
          (coefficientTensorAction ((normalizedInductionFunctor h hU).obj A) x (E t)) g :=
      congrArg (fun s => coefficientTensorMap _ s g) he
    _ = _ := coefficientTensorMap_action _ x (E t) g

end Duality

end Langlands.Plancherel
