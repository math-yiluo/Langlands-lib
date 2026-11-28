import Langlands.Representation.Plancherel.TranslatedCompactCoefficientIntegral

/-! # Evaluation and coefficients of the inverse product left translation -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

universe u uV uW

open CategoryTheory MeasureTheory
open scoped NNReal TensorProduct

namespace Langlands.Plancherel.TranslatedCoefficientValue

open Aubert.General Induction
open ActualConjugateLeviTensor

section Evaluation

variable {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] [SecondCountableTopology H]
  {P M U Q N W : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition Q N W)
  (g : H) (hP : ∀ x : H, x ∈ Q ↔ g⁻¹ * x * g ∈ P)
  (hM : ∀ x : H, x ∈ N ↔ g⁻¹ * x * g ∈ M)
  (hW : ∀ x : H, x ∈ W ↔ g⁻¹ * x * g ∈ U)
  (hc : IsClosed (U : Set H)) (hc' : IsClosed (W : Set H))
  (hu : IsUnimodularModulus U hc) (hu' : IsUnimodularModulus W hc')
  (A : SmoothRep.{0, u, uV} ℂ M)
  [CompactSpace (LeftQuotient P)] [CompactSpace (LeftQuotient Q)]

set_option hygiene false in
local notation "L" => CoefficientConjugation.leviCoefficientLeftTranslation
  h k g hP hM hW hc hc' hu hu' A
set_option quotPrecheck false in
local notation "ρA" => leviInflatedInducingRepresentation (h.prod h) (hc.prod hc)
  (productLeviObject A A.contragredient)
set_option quotPrecheck false in
local notation "ρlA" => leviInflatedInducingRepresentation (k.prod k) (hc'.prod hc')
  (productLeviObject ((conjugationFunctor g hM).obj A)
    ((conjugationFunctor g hM).obj A).contragredient)

/-- The product left translation acts pointwise on the whole product section. -/
theorem leviCoefficientLeftTranslation_eval
    (f : leviProductInducedCoefficientObject h hc A) (x : H × H) :
    Induction.eval (Q.prod Q) ρlA (L f) x =
      conjugateValue g hM A (Induction.eval (P.prod P) ρA f ((g, g)⁻¹ * x)) := by
  let T := leviNormalizedProductInductionTensorEquiv h h hc hc hu hu A A.contragredient
  obtain ⟨v, rfl⟩ := T.surjective f
  let evA := FiniteProductTensorBijective.evalLinear (P.prod P) ρA ((g, g)⁻¹ * x)
  let evB := FiniteProductTensorBijective.evalLinear (Q.prod Q) ρlA x
  have heq : (evB.comp (L).toLinearMap).comp T.toLinearMap =
      ((conjugateValue g hM A).toLinearMap.comp evA).comp T.toLinearMap := by
    apply TensorProduct.ext'
    intro a ℓ
    change Induction.eval (Q.prod Q) ρlA (L (T (a ⊗ₜ[ℂ] ℓ))) x =
      conjugateValue g hM A (Induction.eval (P.prod P) ρA (T (a ⊗ₜ[ℂ] ℓ)) ((g, g)⁻¹ * x))
    exact (CoefficientConjugation.leviCoefficientLeftTranslation_tmul_eval
      h k g hP hM hW hc hc' hu hu' A a ℓ x).trans
      ((congrArg (conjugateValue g hM A)
        (leviNormalizedProductInductionTensorEquiv_tmul_eval h h hc hc hu hu
          A A.contragredient a ℓ ((g, g)⁻¹ * x))).trans rfl).symm
  exact DFunLike.congr_fun heq v

/-- The inverse product left translation acts pointwise on product sections. -/
theorem leviCoefficientLeftTranslation_symm_eval
    (F : leviProductInducedCoefficientObject k hc' ((conjugationFunctor g hM).obj A)) (x : H × H) :
    Induction.eval (P.prod P) ρA ((L).symm F) x =
      (conjugateValue g hM A).symm (Induction.eval (Q.prod Q) ρlA F ((g, g) * x)) := by
  have hx := leviCoefficientLeftTranslation_eval h k g hP hM hW hc hc' hu hu' A ((L).symm F)
    ((g, g) * x)
  rw [Representation.Equiv.apply_symm_apply, inv_mul_cancel_left] at hx
  exact ((conjugateValue g hM A).symm_apply_apply _).symm.trans
    (congrArg (conjugateValue g hM A).symm hx.symm)

omit [LocallyCompactSpace H] [SecondCountableTopology H] in
/-- Coefficient-value conjugation preserves the contraction. -/
theorem conjugateValue_contraction (t : CoefficientTensor A) :
    TensorProduct.lift (smoothDualPairing ((conjugationFunctor g hM).obj A).representation).flip (conjugateValue g hM A t) =
      TensorProduct.lift (smoothDualPairing A.representation).flip t := by
  have hlin : (TensorProduct.lift (smoothDualPairing ((conjugationFunctor g hM).obj A).representation).flip).comp
      (conjugateValue g hM A).toLinearMap =
      TensorProduct.lift (smoothDualPairing A.representation).flip := by
    apply TensorProduct.ext'
    intro a ℓ
    rfl
  exact LinearMap.congr_fun hlin t

end Evaluation

section Integral

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  {P M U Q N W : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition Q N W)
  (K : OpenSubgroup H) (hK : IsCompact (K : Set H)) (g : K)
  (hP : ∀ x : H, x ∈ Q ↔ (g : H)⁻¹ * x * g ∈ P)
  (hM : ∀ x : H, x ∈ N ↔ (g : H)⁻¹ * x * g ∈ M)
  (hW : ∀ x : H, x ∈ W ↔ (g : H)⁻¹ * x * g ∈ U)
  (hc : IsClosed (U : Set H)) (hc' : IsClosed (W : Set H))
  (hu : IsUnimodularModulus U hc) (hu' : IsUnimodularModulus W hc')
  (B : SmoothRep.{0, u, uV} ℂ M) (A : SmoothRep.{0, u, uW} ℂ N)
  (e : A.representation.Equiv ((conjugationFunctor (g : H) hM).obj B).representation)
  [CompactSpace (LeftQuotient P)] [CompactSpace (LeftQuotient Q)]

set_option quotPrecheck false in
local notation "L" => CoefficientConjugation.leviCoefficientLeftTranslation
  h k (g : H) hP hM hW hc hc' hu hu' B

set_option maxHeartbeats 800000 in
/-- An inducing equivalence followed by the inverse product left translation
by a compact point preserves the compact coefficient integral. -/
theorem integral_leviIntegrand_inverseTranslated
    (F : leviProductInducedCoefficientObject k hc' A) (x : H) :
    (∫ l : K, CompactInduction.leviIntegrand h hc B K x
        ((L).symm (coefficientCongr k hc' hu' e F)) l ∂CompactInduction.measure K hK) =
      ∫ l : K, CompactInduction.leviIntegrand k hc' A K x F l ∂CompactInduction.measure K hK := by
  let : BorelSpace K := inferInstanceAs (BorelSpace (K : Subgroup H))
  let : ContinuousMul K := inferInstanceAs (ContinuousMul (K : Subgroup H))
  let : MeasurableMul K :=
    ⟨fun _ => (continuous_const.mul continuous_id).measurable,
      fun _ => (continuous_id.mul continuous_const).measurable⟩
  calc
    _ = ∫ l : K, CompactInduction.leviIntegrand k hc' A K x F (g * l)
          ∂CompactInduction.measure K hK := by
      apply integral_congr_ae
      filter_upwards [] with l
      simp only [CompactInduction.leviIntegrand, leviProductInducedCoefficientIntegrand,
        LinearMap.coe_mk, AddHom.coe_mk]
      have he := leviCoefficientLeftTranslation_symm_eval h k (g : H) hP hM hW hc hc' hu hu' B
        (coefficientCongr k hc' hu' e F) ((l : H) * x, (l : H))
      refine (congrArg
        (fun v : CoefficientTensor B => TensorProduct.lift (smoothDualPairing B.representation).flip v)
        he).trans ?_
      rw [← conjugateValue_contraction (g : H) hM B, LinearEquiv.apply_symm_apply]
      have hcc := coefficientCongr_eval k hc' hu' e F (((g : H), (g : H)) * ((l : H) * x, (l : H)))
      have harg : ((g : H), (g : H)) * ((l : H) * x, (l : H)) =
          (((g * l : K) : H) * x, (g * l : K).val) :=
        Prod.ext (mul_assoc _ _ _).symm rfl
      refine (congrArg (TensorProduct.lift
        (smoothDualPairing ((conjugationFunctor (g : H) hM).obj B).representation).flip) hcc).trans
        ((productCoefficientLeviEquiv_pairing e _).trans ?_)
      exact congrArg (fun p : H × H => TensorProduct.lift (smoothDualPairing A.representation).flip
        (Induction.eval (Q.prod Q) (leviInflatedInducingRepresentation (k.prod k) (hc'.prod hc')
          (productLeviObject A A.contragredient)) F p)) harg
    _ = _ := integral_mul_left_eq_self _ g

set_option maxHeartbeats 800000 in
/-- An inducing equivalence followed by the inverse product left translation
by a compact point preserves the compact probability coefficient map. -/
theorem leviCoefficientMap_inverseTranslated [T2Space H]
    [LocallyCompactSpace P] [LocallyCompactSpace Q]
    (hPc : IsClosed (P : Set H)) (hQc : IsClosed (Q : Set H))
    (hm : Continuous h.projection) (hm' : Continuous k.projection)
    (hPK : ∀ x : H, ∃ q ∈ P, ∃ l ∈ K, x = q * l)
    (hQK : ∀ x : H, ∃ q ∈ Q, ∃ l ∈ K, x = q * l)
    (hG : ∀ x : H, Measure.modularCharacter x = 1)
    (hδ : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hc P h.le_normalizer q : ℝ≥0))
    (hδ' : ∀ q : Q, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter W hc' Q k.le_normalizer q : ℝ≥0))
    (hB : B.IsAdmissible) (hA : A.IsAdmissible)
    (F : leviProductInducedCoefficientObject k hc' A) :
    CompactInduction.leviCoefficientMap h hc B K hu hK hPc hm hPK hG hδ hB
        ((L).symm (coefficientCongr k hc' hu' e F)) =
      CompactInduction.leviCoefficientMap k hc' A K hu' hK hQc hm' hQK hG hδ' hA F := by
  ext x
  rw [CompactInduction.leviCoefficientMap_integral, CompactInduction.leviCoefficientMap_integral]
  exact integral_leviIntegrand_inverseTranslated h k K hK g hP hM hW hc hc' hu hu' B A e F x

end Integral

section IntegralOfMem

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  {P M U Q N W : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition Q N W)
  (K : OpenSubgroup H) (hK : IsCompact (K : Set H)) (g : H) (hg : g ∈ K)
  (hP : ∀ x : H, x ∈ Q ↔ g⁻¹ * x * g ∈ P)
  (hM : ∀ x : H, x ∈ N ↔ g⁻¹ * x * g ∈ M)
  (hW : ∀ x : H, x ∈ W ↔ g⁻¹ * x * g ∈ U)
  (hc : IsClosed (U : Set H)) (hc' : IsClosed (W : Set H))
  (hu : IsUnimodularModulus U hc) (hu' : IsUnimodularModulus W hc')
  (B : SmoothRep.{0, u, uV} ℂ M) (A : SmoothRep.{0, u, uW} ℂ N)
  (e : A.representation.Equiv ((conjugationFunctor g hM).obj B).representation)
  [CompactSpace (LeftQuotient P)] [CompactSpace (LeftQuotient Q)]

include hg in
/-- `leviCoefficientMap_inverseTranslated` for a point of the ambient group
lying in the compact subgroup. -/
theorem leviCoefficientMap_inverseTranslated_of_mem [T2Space H]
    [LocallyCompactSpace P] [LocallyCompactSpace Q]
    (hPc : IsClosed (P : Set H)) (hQc : IsClosed (Q : Set H))
    (hm : Continuous h.projection) (hm' : Continuous k.projection)
    (hPK : ∀ x : H, ∃ q ∈ P, ∃ l ∈ K, x = q * l)
    (hQK : ∀ x : H, ∃ q ∈ Q, ∃ l ∈ K, x = q * l)
    (hG : ∀ x : H, Measure.modularCharacter x = 1)
    (hδ : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hc P h.le_normalizer q : ℝ≥0))
    (hδ' : ∀ q : Q, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter W hc' Q k.le_normalizer q : ℝ≥0))
    (hB : B.IsAdmissible) (hA : A.IsAdmissible)
    (F : leviProductInducedCoefficientObject k hc' A) :
    CompactInduction.leviCoefficientMap h hc B K hu hK hPc hm hPK hG hδ hB
        ((CoefficientConjugation.leviCoefficientLeftTranslation
          h k g hP hM hW hc hc' hu hu' B).symm (coefficientCongr k hc' hu' e F)) =
      CompactInduction.leviCoefficientMap k hc' A K hu' hK hQc hm' hQK hG hδ' hA F :=
  leviCoefficientMap_inverseTranslated h k K hK ⟨g, hg⟩ hP hM hW hc hc' hu hu' B A e
    hPc hQc hm hm' hPK hQK hG hδ hδ' hB hA F

end IntegralOfMem

section UntwistedValue

variable {H : Type u} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  {M N : Subgroup H} {I J : Type*} (ν : I → (M →* ℝ≥0ˣ)) (ν' : J → (N →* ℝ≥0ˣ))
  (g : H) (hM : ∀ x : H, x ∈ N ↔ g⁻¹ * x * g ∈ M)
  (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uW} ℂ N)
  (z : unramifiedCharacters ν) (w : unramifiedCharacters ν')

set_option quotPrecheck false in
local notation "Az" => A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)
set_option quotPrecheck false in
local notation "Bw" => B.twist w.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν' w)

/-- If an inducing equivalence from the conjugate twist to a twist of `B` acts
on vectors as a fixed equivalence `ι` of the untwisted representations, the
removal of the twists turns the coefficient-value transport into the fixed
transport along `ι` after conjugation. -/
theorem untwist_conjugateValue_of_eq
    (ι : ((conjugationFunctor g hM).obj A).representation.Equiv B.representation)
    (e : ((conjugationFunctor g hM).obj Az).representation.Equiv (Bw).representation)
    (he : ∀ v : A, e v = ι v) (v : CoefficientTensor Az) :
    productCompactTwistTensorEquiv ν' w B
        (productCoefficientLeviEquiv e (conjugateValue g hM Az v)) =
      productCoefficientLeviEquiv ι
        (conjugateValue g hM A (productCompactTwistTensorEquiv ν z A v)) := by
  have hEq : (productCompactTwistTensorEquiv ν' w B).toLinearMap.comp
      ((productCoefficientLeviEquiv e).toLinearMap.comp (conjugateValue g hM Az).toLinearMap) =
      (productCoefficientLeviEquiv ι).toLinearMap.comp
        ((conjugateValue g hM A).toLinearMap.comp
          (productCompactTwistTensorEquiv ν z A).toLinearMap) := by
    apply TensorProduct.ext'
    intro a ℓ
    have hs (b : B) : e.symm b = ι.symm b := by
      apply e.injective
      exact (e.apply_symm_apply b).trans
        ((ι.apply_symm_apply b).symm.trans (he (ι.symm b)).symm)
    change e a ⊗ₜ[ℂ] _ = ι a ⊗ₜ[ℂ] _
    rw [he a]
    congr 1
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    change ℓ.val (e.symm b) = ℓ.val (ι.symm b)
    exact congrArg ℓ.val (hs b)
  exact DFunLike.congr_fun hEq v

end UntwistedValue

section UntwistedEvaluation

variable {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] [SecondCountableTopology H]
  {P M U Q N W : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition Q N W)
  (g : H) (hP : ∀ x : H, x ∈ Q ↔ g⁻¹ * x * g ∈ P)
  (hM : ∀ x : H, x ∈ N ↔ g⁻¹ * x * g ∈ M)
  (hW : ∀ x : H, x ∈ W ↔ g⁻¹ * x * g ∈ U)
  (hc : IsClosed (U : Set H)) (hc' : IsClosed (W : Set H))
  (hu : IsUnimodularModulus U hc) (hu' : IsUnimodularModulus W hc')
  [CompactSpace (LeftQuotient P)] [CompactSpace (LeftQuotient Q)]
  {I J : Type*} (ν : I → (M →* ℝ≥0ˣ)) (ν' : J → (N →* ℝ≥0ˣ))
  (A : SmoothRep.{0, u, uV} ℂ M)
  (z : unramifiedCharacters ν) (w : unramifiedCharacters ν')

set_option quotPrecheck false in
local notation "Az" => A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)
set_option quotPrecheck false in
local notation "Agw" => ((conjugationFunctor g hM).obj A).twist w.val.toMonoidHom
  (unramifiedCharacter_isOpen_ker ν' w)

/-- After removal of the twists, the product left translation followed by an
inducing equivalence with identity vector map acts on values as the fixed
coefficient-value conjugation at the left translate. -/
theorem untwist_translated_eval
    (e : ((conjugationFunctor g hM).obj Az).representation.Equiv (Agw).representation)
    (he : HEq e.toLinearEquiv (LinearEquiv.refl ℂ A))
    (f : leviProductInducedCoefficientObject h hc Az) (x : H × H) :
    productCompactTwistTensorEquiv ν' w ((conjugationFunctor g hM).obj A)
        (Induction.eval (Q.prod Q)
          (leviInflatedInducingRepresentation (k.prod k) (hc'.prod hc')
            (productLeviObject Agw (Agw).contragredient))
          (coefficientCongr k hc' hu' e
            (CoefficientConjugation.leviCoefficientLeftTranslation h k g hP hM hW hc hc' hu hu'
              Az f)) x) =
      conjugateValue g hM A (productCompactTwistTensorEquiv ν z A
        (Induction.eval (P.prod P)
          (leviInflatedInducingRepresentation (h.prod h) (hc.prod hc)
            (productLeviObject Az (Az).contragredient)) f ((g, g)⁻¹ * x))) := by
  have h' : e.toLinearEquiv = LinearEquiv.refl ℂ A := eq_of_heq he
  exact (congrArg (productCompactTwistTensorEquiv ν' w ((conjugationFunctor g hM).obj A))
    ((coefficientCongr_eval k hc' hu' e _ x).trans (congrArg (productCoefficientLeviEquiv e)
      (leviCoefficientLeftTranslation_eval h k g hP hM hW hc hc' hu hu' _ f x)))).trans
    (untwist_conjugateValue ν ν' g hM A z w e (fun v => DFunLike.congr_fun h' v) _)

omit [LocallyCompactSpace H] [SecondCountableTopology H] in
/-- Transport of coefficient tensors along an equivalence and back along its
inverse is the identity. -/
theorem productCoefficientLeviEquiv_symm_apply_apply {M : Subgroup H}
    {X : SmoothRep.{0, u, uV} ℂ M} {Y : SmoothRep.{0, u, uW} ℂ M}
    (e : X.representation.Equiv Y.representation) (t) :
    productCoefficientLeviEquiv e.symm (productCoefficientLeviEquiv e t) = t := by
  have hrefl : e.trans e.symm = Representation.Equiv.refl X.representation := by
    ext v
    exact e.symm_apply_apply v
  have h1 := coefficientTensorCongr_trans e e.symm t
  rw [hrefl] at h1
  exact ((coefficientTensorCongr_refl t).symm.trans h1).symm

omit [LocallyCompactSpace H] [SecondCountableTopology H] in
/-- The identity vector map between two pullbacks along pointwise equal
isomorphisms. -/
def pullbackCongrEquiv {M N : Subgroup H} (e e' : N ≃ₜ* M) (B : SmoothRep.{0, u, uV} ℂ M)
    (he : ∀ n, e n = e' n) :
    (SmoothRep.pullback e B).representation.Equiv (SmoothRep.pullback e' B).representation where
  toLinearEquiv := LinearEquiv.refl ℂ B
  isIntertwining' n := by
    ext v
    change B.representation (e n) v = B.representation (e' n) v
    rw [he]

omit [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H] in
/-- `pullbackCongrEquiv` is the identity linear map of the carrier. -/
theorem pullbackCongrEquiv_symm_linear_heq {M N : Subgroup H} (e e' : N ≃ₜ* M)
    (B : SmoothRep.{0, u, uV} ℂ M) (he : ∀ n, e n = e' n) :
    HEq (pullbackCongrEquiv e e' B he).symm.toLinearEquiv (LinearEquiv.refl ℂ B) :=
  HEq.rfl

omit [LocallyCompactSpace H] [SecondCountableTopology H] in
/-- The identity vector map from a pullback to a twofold pullback along
pointwise equal isomorphisms. -/
def pullbackPullbackCongrEquiv {L M N : Subgroup H} (e : N ≃ₜ* L) (e₁ : M ≃ₜ* L)
    (e₂ : N ≃ₜ* M) (B : SmoothRep.{0, u, uV} ℂ L) (he : ∀ n, e n = e₁ (e₂ n)) :
    (SmoothRep.pullback e B).representation.Equiv
      (SmoothRep.pullback e₂ (SmoothRep.pullback e₁ B)).representation where
  toLinearEquiv := LinearEquiv.refl ℂ B
  isIntertwining' n := by
    ext v
    change B.representation (e n) v = B.representation (e₁ (e₂ n)) v
    rw [he]

omit [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H] in
/-- `pullbackPullbackCongrEquiv` is the identity linear map of the carrier. -/
theorem pullbackPullbackCongrEquiv_symm_linear_heq {L M N : Subgroup H} (e : N ≃ₜ* L)
    (e₁ : M ≃ₜ* L) (e₂ : N ≃ₜ* M) (B : SmoothRep.{0, u, uV} ℂ L)
    (he : ∀ n, e n = e₁ (e₂ n)) :
    HEq (pullbackPullbackCongrEquiv e e₁ e₂ B he).symm.toLinearEquiv (LinearEquiv.refl ℂ B) :=
  HEq.rfl

omit [LocallyCompactSpace H] [SecondCountableTopology H] in
/-- The identity vector map between two twofold pullbacks along pointwise
equal composites. -/
def pullbackTwiceCongrEquiv {L M M' N : Subgroup H} (a₁ : M ≃ₜ* L) (a₂ : N ≃ₜ* M)
    (b₁ : M' ≃ₜ* L) (b₂ : N ≃ₜ* M') (B : SmoothRep.{0, u, uV} ℂ L)
    (he : ∀ n, a₁ (a₂ n) = b₁ (b₂ n)) :
    (SmoothRep.pullback a₂ (SmoothRep.pullback a₁ B)).representation.Equiv
      (SmoothRep.pullback b₂ (SmoothRep.pullback b₁ B)).representation where
  toLinearEquiv := LinearEquiv.refl ℂ B
  isIntertwining' n := by
    ext v
    change B.representation (a₁ (a₂ n)) v = B.representation (b₁ (b₂ n)) v
    rw [he]

omit [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H] in
/-- `pullbackTwiceCongrEquiv` is the identity linear map of the carrier. -/
theorem pullbackTwiceCongrEquiv_symm_linear_heq {L M M' N : Subgroup H} (a₁ : M ≃ₜ* L)
    (a₂ : N ≃ₜ* M) (b₁ : M' ≃ₜ* L) (b₂ : N ≃ₜ* M') (B : SmoothRep.{0, u, uV} ℂ L)
    (he : ∀ n, a₁ (a₂ n) = b₁ (b₂ n)) :
    HEq (pullbackTwiceCongrEquiv a₁ a₂ b₁ b₂ B he).symm.toLinearEquiv
      (LinearEquiv.refl ℂ B) :=
  HEq.rfl

set_option quotPrecheck false in
local notation "Bw" B => (B).twist w.val.toMonoidHom
  (unramifiedCharacter_isOpen_ker ν' w)

/-- Suppose the inducing equivalence `E` onto the conjugate twist has the
underlying linear map of `ι.symm`. For the composite of `coefficientCongr`
along `E` and inverse product left translation, the conjugated untwisted
output at `x` equals `productCoefficientLeviEquiv ι.symm` of the untwisted
input evaluated at the left multiple `(g, g) * x`. -/
theorem untwist_inverseTranslated_eval (B : SmoothRep.{0, u, uW} ℂ N)
    (ι : ((conjugationFunctor g hM).obj A).representation.Equiv B.representation)
    (E : (Bw B).representation.Equiv ((conjugationFunctor g hM).obj Az).representation)
    (hE : HEq E.toLinearEquiv ι.symm.toLinearEquiv)
    (F : leviProductInducedCoefficientObject k hc' (Bw B)) (x y : H × H) (hy : (g, g) * x = y) :
    conjugateValue g hM A (productCompactTwistTensorEquiv ν z A
        (Induction.eval (P.prod P)
          (leviInflatedInducingRepresentation (h.prod h) (hc.prod hc)
            (productLeviObject Az (Az).contragredient))
          ((CoefficientConjugation.leviCoefficientLeftTranslation h k g hP hM hW hc hc' hu hu'
              Az).symm (coefficientCongr k hc' hu' E F)) x)) =
      productCoefficientLeviEquiv ι.symm
        (productCompactTwistTensorEquiv ν' w B
          (Induction.eval (Q.prod Q)
            (leviInflatedInducingRepresentation (k.prod k) (hc'.prod hc')
              (productLeviObject (Bw B) (Bw B).contragredient)) F y)) := by
  subst hy
  have h' : E.toLinearEquiv = ι.symm.toLinearEquiv := eq_of_heq hE
  have hs : ∀ v : A, E.symm v = ι v := by
    intro v
    apply E.injective
    exact (E.apply_symm_apply v).trans
      ((ι.symm_apply_apply v).symm.trans (DFunLike.congr_fun h' (ι v)).symm)
  have hval : ∀ t, conjugateValue g hM A (productCompactTwistTensorEquiv ν z A
      ((conjugateValue g hM Az).symm (productCoefficientLeviEquiv E t))) =
      productCoefficientLeviEquiv ι.symm (productCompactTwistTensorEquiv ν' w B t) := by
    intro t
    have key := untwist_conjugateValue_of_eq ν ν' g hM A B z w ι E.symm hs
      ((conjugateValue g hM Az).symm (productCoefficientLeviEquiv E t))
    have e1 : (conjugateValue g hM Az) ((conjugateValue g hM Az).symm
        (productCoefficientLeviEquiv E t)) = productCoefficientLeviEquiv E t :=
      LinearEquiv.apply_symm_apply _ _
    have key' := ((congrArg (fun s => productCompactTwistTensorEquiv ν' w B
        (productCoefficientLeviEquiv E.symm s)) e1).trans
      (congrArg (productCompactTwistTensorEquiv ν' w B)
        (productCoefficientLeviEquiv_symm_apply_apply E t))).symm.trans key
    exact ((congrArg (productCoefficientLeviEquiv ι.symm) key').trans
      (productCoefficientLeviEquiv_symm_apply_apply _ _)).symm
  exact (congrArg (fun s => conjugateValue g hM A (productCompactTwistTensorEquiv ν z A s))
    ((leviCoefficientLeftTranslation_symm_eval h k g hP hM hW hc hc' hu hu' _
      (coefficientCongr k hc' hu' E F) x).trans
      (congrArg (conjugateValue g hM Az).symm (coefficientCongr_eval k hc' hu' E F _)))).trans
    (hval _)

end UntwistedEvaluation

end Langlands.Plancherel.TranslatedCoefficientValue
