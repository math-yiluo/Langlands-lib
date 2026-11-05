import Langlands.Representation.Plancherel.ProductInducedOrbitCompactAction
import Langlands.Representation.Plancherel.FiniteSmoothCompactEvaluation
import Langlands.Representation.Plancherel.UnitaryUnramifiedSmoothEvaluation
import Langlands.Representation.Smooth.SmoothPart.BasicProof

/-! # Full product action on the existing smooth actual orbit sections -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory MeasureTheory
open scoped NNReal ENNReal TensorProduct

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz Induction CompactInduction

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

set_option backward.isDefEq.respectTransparency false in
/-- Removing the twist conjugates full normalized inducing covariance into
one actual Laurent scalar times the unchanged untwisted inducing operator. -/
theorem productCompactTwistTensorEquiv_inducing
    (χ : unramifiedCharacters ν) (A : SmoothRep.{0, uG, uV} ℂ M)
    (p : P.prod P)
    (t : CoefficientTensor
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    productCompactTwistTensorEquiv ν χ A
        (inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject
            (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
            (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).contragredient) p t) =
      (χ.val (h.projection ⟨p.val.1, p.property.1⟩ *
        (h.projection ⟨p.val.2, p.property.2⟩)⁻¹) : ℂ) •
        inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject A A.contragredient) p
          (productCompactTwistTensorEquiv ν χ A t) := by
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [map_add, ht, hs, smul_add]
  | tmul v ℓ =>
    let p₁ : P := ⟨p.val.1, p.property.1⟩
    let p₂ : P := ⟨p.val.2, p.property.2⟩
    let D := smoothContragredientTwistEquiv χ.val.toMonoidHom A.representation
      (unramifiedCharacter_isOpen_ker ν χ)
    have hD := congrArg (fun T => T ℓ) (D.isIntertwining' (h.projection p₂))
    change D (smoothContragredient
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation
          (h.projection p₂) ℓ) =
      ((χ.val (h.projection p₂))⁻¹ : ℂˣ) •
        smoothContragredient A.representation (h.projection p₂) (D ℓ) at hD
    change productCompactTwistTensorEquiv ν χ A
        (((HaarModulus.closedHalfCharacter (U.prod U) (hU.prod hU) (P.prod P)
          (h.prod h).le_normalizer p : ℂˣ) : ℂ) •
          (productLeviObject
            (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
            (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).contragredient).representation
            ((h.prod h).projection p) (v ⊗ₜ[ℂ] ℓ)) =
      (χ.val (h.projection p₁ * (h.projection p₂)⁻¹) : ℂ) •
        (((HaarModulus.closedHalfCharacter (U.prod U) (hU.prod hU) (P.prod P)
          (h.prod h).le_normalizer p : ℂˣ) : ℂ) •
          (productLeviObject A A.contragredient).representation ((h.prod h).projection p)
            (productCompactTwistTensorEquiv ν χ A (v ⊗ₜ[ℂ] ℓ)))
    rw [map_smul, h.prod_projection h p]
    change ((HaarModulus.closedHalfCharacter (U.prod U) (hU.prod hU) (P.prod P)
        (h.prod h).le_normalizer p : ℂˣ) : ℂ) •
      (((χ.val (h.projection p₁) : ℂ) • A.representation (h.projection p₁) v) ⊗ₜ[ℂ]
        D (smoothContragredient
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation
            (h.projection p₂) ℓ)) =
      (χ.val (h.projection p₁ * (h.projection p₂)⁻¹) : ℂ) •
        (((HaarModulus.closedHalfCharacter (U.prod U) (hU.prod hU) (P.prod P)
          (h.prod h).le_normalizer p : ℂˣ) : ℂ) •
          (A.representation (h.projection p₁) v ⊗ₜ[ℂ]
            smoothContragredient A.representation (h.projection p₂) (D ℓ)))
    rw [hD]
    simp only [Units.smul_def, TensorProduct.smul_tmul_smul, smul_smul,
      map_mul, map_inv, Units.val_mul]
    congr 1
    ring

/-- Literal compact evaluation as a linear map. -/
def productInducedCompactEvaluation (K : OpenSubgroup G)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    ProductInducedCompactPicture h K A →ₗ[ℂ] ((K.prod K) → CoefficientTensor A) where
  toFun F k := eval _ _ F k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [LocallyCompactSpace G] in
/-- Literal evaluations distinguish the actual compact induced functions. -/
theorem productInducedCompactEvaluation_injective (K : OpenSubgroup G)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    Function.Injective (productInducedCompactEvaluation h K A) := by
  intro F H hFH
  apply Subtype.ext
  apply Subtype.ext
  exact hFH

variable (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G))
  (hK : IsCompact (K : Set G)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

set_option backward.isDefEq.respectTransparency false in
omit [Fintype J] in
/-- A fixed factorization of k*x gives the literal evaluation of a translated
compact restriction, with choices made independently of the torus parameter. -/
theorem productInducedOrbitRepresentation_full_restriction_eval
    (x : G × G) (k : K.prod K) (p : P.prod P) (l : K.prod K)
    (hkx : (k : G × G) * x = (p : G × G) * (l : G × G))
    (q : ProductInducedOrbitSections ν π h hU) (z : J → Circle) :
    productInducedCompactEvaluation h K π.obj
        (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
          (productInducedOrbitPullback ν π e h hU
            (productInducedOrbitRepresentation h hU ν π x q)) z) k =
      ((e.symm z).val (h.projection ⟨p.val.1, p.property.1⟩ *
        (h.projection ⟨p.val.2, p.property.2⟩)⁻¹) : ℂ) •
        inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject π.obj π.obj.contragredient) p
          (productInducedCompactEvaluation h K π.obj
            (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
              (productInducedOrbitPullback ν π e h hU q) z) l) := by
  change productCompactTwistTensorEquiv ν (unitaryTorusParameter ν e z) π.obj
    (eval _ _ (q (unitaryOrbitParameterRepresentative ν π e z))
      ((k : G × G) * x)) = _
  rw [hkx]
  exact (congrArg (productCompactTwistTensorEquiv ν (unitaryTorusParameter ν e z) π.obj)
    ((q (unitaryOrbitParameterRepresentative ν π e z)).val.property p (l : G × G))).trans
      (productCompactTwistTensorEquiv_inducing h hU ν
        (unitaryTorusParameter ν e z) π.obj p _)

/-- Every fixed compact evaluation of a translated smooth section is a finite
scalar-smooth family, by its actual Laurent covariance formula. -/
theorem productInducedOrbitRepresentation_full_evaluation_mem
    (he : HasLaurentUnitaryCoordinates ν e) (x : G × G)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (k : K.prod K) :
    (fun z => productInducedCompactEvaluation h K π.obj
      (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π e h hU
          (productInducedOrbitRepresentation h hU ν π x q.val)) z) k) ∈
      finiteSmoothFamilies J (CoefficientTensor π.obj) := by
  obtain ⟨p, l, hpl⟩ := product_compact_factorization K hPK ((k : G × G) * x)
  let T : ProductInducedCompactPicture h K π.obj →ₗ[ℂ] CoefficientTensor π.obj :=
    (inducingRepresentation (h.prod h) (hU.prod hU)
      (productLeviObject π.obj π.obj.contragredient) p).comp
      ((LinearMap.proj l).comp (productInducedCompactEvaluation h K π.obj))
  have ht := mem_finiteSmoothFamilies_smul
    (mem_finiteSmoothFamilies_linearMap q.property.2 T)
    (unitaryUnramifiedSmoothEvaluation ν e he
      (h.projection ⟨p.val.1, p.property.1⟩ * (h.projection ⟨p.val.2, p.property.2⟩)⁻¹))
  have heq := funext (productInducedOrbitRepresentation_full_restriction_eval
    h hU ν π K hP hK hν hr hPK e x k p l hpl q.val)
  rw [heq]
  exact ht

/-- The full product group preserves the existing parameter-smooth section
submodule. The finite expansion is recovered from a common open stabilizer. -/
theorem productInducedOrbitRepresentation_full_smooth_mem
    (he : HasLaurentUnitaryCoordinates ν e) (x : G × G)
    {q : ProductInducedOrbitSections ν π h hU}
    (hq : q ∈ productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    productInducedOrbitRepresentation h hU ν π x q ∈
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK := by
  refine ⟨productInducedOrbitRepresentation_coherent h hU ν π x hq.1, ?_⟩
  let F : (J → Circle) → ProductInducedCompactPicture h K π.obj :=
    productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
      (productInducedOrbitPullback ν π e h hU
        (productInducedOrbitRepresentation h hU ν π x q))
  obtain ⟨L, hL⟩ := Langlands.isSmoothVector_apply x
    (productInducedSmoothOrbitSections_isSmoothVector h hU ν π K hP hK hν hr hPK e ⟨q, hq⟩)
  let Lk : OpenSubgroup (K.prod K) := OpenSubgroup.comap
    (K.prod K).toSubgroup.subtype continuous_subtype_val L
  let : CompactSpace (K.prod K) := isCompact_iff_compactSpace.mp (hK.prod hK)
  let : IsTopologicalGroup (K.prod K) :=
    inferInstanceAs (IsTopologicalGroup (K.prod K).toSubgroup)
  change F ∈ finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj)
  apply mem_finiteSmoothFamilies_of_common_open_stabilizer
    (productInducedCompactEvaluation h K π.obj)
    (productInducedCompactEvaluation_injective h K π.obj) F Lk
  · intro z k l
    have hraw := hL ⟨((l : K.prod K) : G × G), l.property⟩
    have hfix : productInducedCompactRepresentation h K π.obj (l : K.prod K) (F z) = F z :=
      (productInducedOrbitRepresentation_restriction h hU ν π K hP hK hν hr hPK e
        l.val (productInducedOrbitRepresentation h hU ν π x q) z).symm.trans
        (congrArg (fun s => productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
          (productInducedOrbitPullback ν π e h hU s) z) hraw)
    exact congrArg (fun v : ProductInducedCompactPicture h K π.obj =>
      Induction.eval _ _ v k) hfix
  · exact productInducedOrbitRepresentation_full_evaluation_mem h hU ν π K hP hK hν hr hPK e he x ⟨q, hq⟩

/-- The full actual product action on precisely the existing smooth sections. -/
def productInducedSmoothOrbitRepresentation (he : HasLaurentUnitaryCoordinates ν e) :
    Representation ℂ (G × G)
      (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :=
  Representation.subrepresentation (productInducedOrbitRepresentation h hU ν π)
    (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (fun x _ hq => productInducedOrbitRepresentation_full_smooth_mem
      h hU ν π K hP hK hν hr hPK e he x hq)

@[simp]
theorem productInducedSmoothOrbitRepresentation_apply
    (he : HasLaurentUnitaryCoordinates ν e) (x : G × G)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (A : UnitaryOrbitRepresentative ν π) :
    (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e he x q).val A =
      (productInducedCoefficientObject h hU A.val.obj).representation x (q.val A) := rfl

/-- The full action is literally right translation on each normalized induced function. -/
theorem productInducedSmoothOrbitRepresentation_eval
    (he : HasLaurentUnitaryCoordinates ν e) (x : G × G)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (A : UnitaryOrbitRepresentative ν π) (y : G × G) :
    eval _ _ ((productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e he x q).val A) y =
      eval _ _ (q.val A) (y * x) := rfl

/-- Ambient smoothness now supplies smoothness of the proved full subrepresentation. -/
theorem productInducedSmoothOrbitRepresentation_isSmooth
    (he : HasLaurentUnitaryCoordinates ν e) :
    IsSmooth (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e he) := by
  intro q
  obtain ⟨L, hL⟩ := productInducedSmoothOrbitSections_isSmoothVector
    h hU ν π K hP hK hν hr hPK e q
  exact ⟨L, fun l => Subtype.ext (hL l)⟩

/-- The full action bundled in the canonical smooth representation category. -/
def productInducedSmoothOrbitObject (he : HasLaurentUnitaryCoordinates ν e) :
    SmoothRep ℂ (G × G) :=
  ⟨Rep.of (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e he),
    productInducedSmoothOrbitRepresentation_isSmooth h hU ν π K hP hK hν hr hPK e he⟩

/-- Restricting the full action recovers the original compact action. -/
@[simp]
theorem productInducedSmoothOrbitRepresentation_compact
    (he : HasLaurentUnitaryCoordinates ν e) :
    (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e he).comp
        (K.prod K).toSubgroup.subtype =
      productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e := rfl

section OrbitForm

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

/-- Full invariance holds at every actual orbit class for the original
inverse-degree fiber pairings. -/
theorem unitaryOrbitProductPairing_full_action
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (x : G × G)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e
        (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e hLaurent x q)
        (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e hLaurent x r) ω =
      unitaryOrbitProductPairing
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r ω := by
  obtain ⟨A, rfl⟩ :=
    unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω
  rw [unitaryOrbitProductPairing_representative, unitaryOrbitProductPairing_representative]
  exact (unitaryOrbitRepresentativeProductForm
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν A).invariant x (q.val A) (r.val A)

variable [Finite (M ⧸ (commonNormKernel ν ⊔ C))]

/-- The full action preserves the entire original orbit-integral core, with
its original orbit measure, scale and inverse-degree fiber forms. -/
theorem productInducedSmoothOrbitCore_full_action
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure] (x : G × G)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (productInducedSmoothOrbitCore
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η).inner
        (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e hLaurent x q)
        (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e hLaurent x r) =
      (productInducedSmoothOrbitCore
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η).inner q r := by
  rw [productInducedSmoothOrbitCore_inner_integral, productInducedSmoothOrbitCore_inner_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (unitaryOrbitProductPairing_full_action
      h hU ν π K hP hK hν hr hPK e hG hδ hcof C hC μ hsq hLaurent x q r)

/-- The canonical positive orbit-integral form with full product-group invariance. -/
def productInducedSmoothOrbitForm
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure] :
    InvariantPositiveForm
      (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e hLaurent) where
  toInnerProductCore := productInducedSmoothOrbitCore
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η
  invariant := productInducedSmoothOrbitCore_full_action
    h hU ν π K hP hK hν hr hPK e hG hδ hcof C hC μ hsq hLaurent he η

/-- Adding full invariance leaves the original whole core definitionally unchanged. -/
@[simp]
theorem productInducedSmoothOrbitForm_toInnerProductCore
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure] :
    (productInducedSmoothOrbitForm
      h hU ν π K hP hK hν hr hPK e hG hδ hcof C hC μ hsq hLaurent he η).toInnerProductCore =
      productInducedSmoothOrbitCore
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η := rfl

end OrbitForm

end Langlands.Plancherel
