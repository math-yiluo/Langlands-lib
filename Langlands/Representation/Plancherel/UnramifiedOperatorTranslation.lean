import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation
import Mathlib.Topology.Algebra.Group.CompactOpen

/-! # Translation of actual unramified operator parameters -/

noncomputable section

open scoped NNReal BigOperators

namespace Langlands.Plancherel

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

/-- Multiplying the parameter by a fixed unramified character is a
homeomorphism of the actual full character space. -/
def unramifiedParameterTranslation (τ : unramifiedCharacters ν) :
    unramifiedCharacters ν ≃ₜ unramifiedCharacters ν :=
  Homeomorph.mulLeft τ

@[simp]
theorem unramifiedParameterTranslation_apply
    (τ χ : unramifiedCharacters ν) :
    unramifiedParameterTranslation ν τ χ = τ * χ := rfl

@[simp]
theorem unramifiedParameterTranslation_symm_apply
    (τ χ : unramifiedCharacters ν) :
    (unramifiedParameterTranslation ν τ).symm χ = τ⁻¹ * χ := rfl

private def translationFunctionAlgEquiv (τ : unramifiedCharacters ν) :
    (unramifiedCharacters ν → ℂ) ≃ₐ[ℂ] (unramifiedCharacters ν → ℂ) where
  toFun f χ := f (τ * χ)
  invFun f χ := f (τ⁻¹ * χ)
  left_inv f := by funext χ; simp
  right_inv f := by funext χ; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem translationFunctionAlgEquiv_evaluation
    (τ : unramifiedCharacters ν) (g : G) :
    translationFunctionAlgEquiv ν τ (unramifiedEvaluation ν g) =
      (τ.val g : ℂ) • unramifiedEvaluation ν g := by
  funext χ
  change ((τ.val g * χ.val g : ℂˣ) : ℂ) = _
  simp [unramifiedEvaluation]

private theorem translationFunctionAlgEquiv_mem
    (τ : unramifiedCharacters ν) (b : unramifiedRegularFunctions ν) :
    translationFunctionAlgEquiv ν τ b.val ∈ unramifiedRegularFunctions ν := by
  change b.val ∈ (unramifiedRegularFunctions ν).comap
    (translationFunctionAlgEquiv ν τ).toAlgHom
  refine Algebra.adjoin_le (S := (unramifiedRegularFunctions ν).comap
    (translationFunctionAlgEquiv ν τ).toAlgHom) ?_ b.property
  rintro _ ⟨g, rfl⟩
  change translationFunctionAlgEquiv ν τ (unramifiedEvaluation ν g) ∈
    unramifiedRegularFunctions ν
  rw [translationFunctionAlgEquiv_evaluation]
  exact (unramifiedRegularFunctions ν).smul_mem
    (unramifiedEvaluationRegular ν g).property _

/-- Pullback `b(χ) ↦ b(τχ)` preserves the actual evaluation-generated
regular algebra; it scales each evaluation by `τ(g)`. -/
def unramifiedRegularTranslation (τ : unramifiedCharacters ν) :
    unramifiedRegularFunctions ν ≃ₐ[ℂ] unramifiedRegularFunctions ν where
  toFun b := ⟨translationFunctionAlgEquiv ν τ b.val,
    translationFunctionAlgEquiv_mem ν τ b⟩
  invFun b := ⟨translationFunctionAlgEquiv ν τ⁻¹ b.val,
    translationFunctionAlgEquiv_mem ν τ⁻¹ b⟩
  left_inv b := by
    apply Subtype.ext
    exact (translationFunctionAlgEquiv ν τ).left_inv b.val
  right_inv b := by
    apply Subtype.ext
    exact (translationFunctionAlgEquiv ν τ).right_inv b.val
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem unramifiedRegularTranslation_apply
    (τ : unramifiedCharacters ν) (b : unramifiedRegularFunctions ν)
    (χ : unramifiedCharacters ν) :
    (unramifiedRegularTranslation ν τ b).val χ = b.val (τ * χ) := rfl

@[simp]
theorem unramifiedRegularTranslation_symm_apply
    (τ : unramifiedCharacters ν) (b : unramifiedRegularFunctions ν)
    (χ : unramifiedCharacters ν) :
    ((unramifiedRegularTranslation ν τ).symm b).val χ = b.val (τ⁻¹ * χ) := rfl

@[simp]
theorem unramifiedRegularTranslation_evaluation
    (τ : unramifiedCharacters ν) (g : G) :
    unramifiedRegularTranslation ν τ (unramifiedEvaluationRegular ν g) =
      (τ.val g : ℂ) • unramifiedEvaluationRegular ν g := by
  apply Subtype.ext
  exact translationFunctionAlgEquiv_evaluation ν τ g

/-- Exact restriction of parameter translation to the preimage of a region. -/
def unramifiedTranslationPreimageEquiv
    (τ : unramifiedCharacters ν) (Ω : Set (unramifiedCharacters ν)) :
    ((unramifiedParameterTranslation ν τ) ⁻¹' Ω) ≃ Ω :=
  (unramifiedParameterTranslation ν τ).toEquiv.subtypeEquiv (fun _ => Iff.rfl)

@[simp]
theorem unramifiedTranslationPreimageEquiv_apply
    (τ : unramifiedCharacters ν) (Ω : Set (unramifiedCharacters ν))
    (χ : (unramifiedParameterTranslation ν τ) ⁻¹' Ω) :
    (unramifiedTranslationPreimageEquiv ν τ Ω χ).val = τ * χ.val := rfl

@[simp]
theorem unramifiedTranslationPreimageEquiv_symm_apply
    (τ : unramifiedCharacters ν) (Ω : Set (unramifiedCharacters ν)) (χ : Ω) :
    ((unramifiedTranslationPreimageEquiv ν τ Ω).symm χ).val = τ⁻¹ * χ.val := rfl

namespace UnramifiedOperatorFamily

variable {ν}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (τ : unramifiedCharacters ν) (Ω : Set (unramifiedCharacters ν))

/-- Parameter translation preserves and reflects finite expansions in fixed
vectors, with translated regular coefficients. -/
theorem isPolynomialOn_translation_iff (f : Ω → V) :
    IsPolynomialOn ((unramifiedParameterTranslation ν τ) ⁻¹' Ω)
        (fun χ => f (unramifiedTranslationPreimageEquiv ν τ Ω χ)) ↔
      IsPolynomialOn Ω f := by
  constructor
  · rintro ⟨n, b, v, hf⟩
    refine ⟨n, fun i => unramifiedRegularTranslation ν τ⁻¹ (b i), v, ?_⟩
    intro χ
    have h := hf ((unramifiedTranslationPreimageEquiv ν τ Ω).symm χ)
    simpa only [Equiv.apply_symm_apply, unramifiedRegularTranslation_apply,
      unramifiedTranslationPreimageEquiv_symm_apply] using h
  · rintro ⟨n, b, v, hf⟩
    refine ⟨n, fun i => unramifiedRegularTranslation ν τ (b i), v, ?_⟩
    intro χ
    simpa only [unramifiedRegularTranslation_apply,
      unramifiedTranslationPreimageEquiv_apply] using
        hf (unramifiedTranslationPreimageEquiv ν τ Ω χ)

theorem isPolynomialOperatorOn_translation_iff (A : Ω → V →ₗ[ℂ] W) :
    IsPolynomialOperatorOn ((unramifiedParameterTranslation ν τ) ⁻¹' Ω)
        (fun χ => A (unramifiedTranslationPreimageEquiv ν τ Ω χ)) ↔
      IsPolynomialOperatorOn Ω A :=
  forall_congr' (fun v => isPolynomialOn_translation_iff τ Ω (fun χ => A χ v))

/-- Translate the one denominator chosen before quantifying over all input
vectors; this is whole-operator rationality in both directions. -/
theorem isRationalOperatorOn_translation_iff (A : Ω → V →ₗ[ℂ] W) :
    IsRationalOperatorOn ((unramifiedParameterTranslation ν τ) ⁻¹' Ω)
        (fun χ => A (unramifiedTranslationPreimageEquiv ν τ Ω χ)) ↔
      IsRationalOperatorOn Ω A := by
  constructor
  · rintro ⟨b, hb, hA⟩
    refine ⟨(unramifiedRegularTranslation ν τ).symm b, ?_, ?_⟩
    · intro χ
      simpa only [unramifiedRegularTranslation_symm_apply,
        unramifiedTranslationPreimageEquiv_symm_apply] using
          hb ((unramifiedTranslationPreimageEquiv ν τ Ω).symm χ)
    · apply (isPolynomialOperatorOn_translation_iff τ Ω _).mp
      simpa only [unramifiedRegularTranslation_symm_apply,
        unramifiedTranslationPreimageEquiv_apply, inv_mul_cancel_left] using hA
  · rintro ⟨b, hb, hA⟩
    refine ⟨unramifiedRegularTranslation ν τ b, ?_, ?_⟩
    · intro χ
      simpa only [unramifiedRegularTranslation_apply,
        unramifiedTranslationPreimageEquiv_apply] using
          hb (unramifiedTranslationPreimageEquiv ν τ Ω χ)
    · simpa only [unramifiedRegularTranslation_apply,
        unramifiedTranslationPreimageEquiv_apply] using
          (isPolynomialOperatorOn_translation_iff τ Ω
            (fun χ => b.val χ.val • A χ)).mpr hA

namespace RationalOperatorContinuationData

variable {Ω} {A : Ω → V →ₗ[ℂ] W} (p : RationalOperatorContinuationData Ω A)

/-- Translate existing continuation data, including its chosen denominator
and the same globally linear polynomial numerator. -/
def translation :
    RationalOperatorContinuationData ((unramifiedParameterTranslation ν τ) ⁻¹' Ω)
      (fun χ => A (unramifiedTranslationPreimageEquiv ν τ Ω χ)) where
  denominator := unramifiedRegularTranslation ν τ p.denominator
  denominator_nonzero χ := p.denominator_nonzero
    (unramifiedTranslationPreimageEquiv ν τ Ω χ)
  numerator χ := p.numerator (τ * χ)
  polynomial v := by
    obtain ⟨n, b, w, hw⟩ := p.polynomial v
    exact ⟨n, fun i => unramifiedRegularTranslation ν τ (b i), w,
      fun χ => hw ⟨τ * χ.val, Set.mem_univ _⟩⟩
  clears χ := p.clears (unramifiedTranslationPreimageEquiv ν τ Ω χ)

/-- The regular region is exactly the translated preimage, not a newly
chosen or enlarged locus. -/
theorem translation_regularRegion :
    (p.translation τ).regularRegion =
      (unramifiedParameterTranslation ν τ) ⁻¹' p.regularRegion := rfl

/-- Continuation commutes with parameter translation at every regular value. -/
theorem translation_continuedOperator
    (χ : (p.translation τ).regularRegion) :
    (p.translation τ).continuedOperator χ =
      p.continuedOperator ⟨τ * χ.val, χ.property⟩ := rfl

end RationalOperatorContinuationData

end UnramifiedOperatorFamily

end Langlands.Plancherel
