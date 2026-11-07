import Langlands.Representation.Plancherel.UnramifiedOperatorTranslation
import Langlands.Representation.Plancherel.RationalUnramifiedScalarField

/-! # Translation of actual unramified rational scalars -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uG uI uV

section Generic

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)}

@[simp]
theorem unramifiedRegularTranslation_one :
    unramifiedRegularTranslation ν 1 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro b
  apply Subtype.ext
  funext χ
  change b.val (1 * χ) = b.val χ
  rw [one_mul]

theorem unramifiedRegularTranslation_mul (τ σ : unramifiedCharacters ν) :
    unramifiedRegularTranslation ν (τ * σ) =
      (unramifiedRegularTranslation ν τ).trans (unramifiedRegularTranslation ν σ) := by
  apply AlgEquiv.ext
  intro b
  apply Subtype.ext
  funext χ
  change b.val ((τ * σ) * χ) = b.val (τ * (σ * χ))
  rw [mul_assoc]

namespace UnramifiedOperatorFamily.ScalarPresentation

variable {Ω : Set (unramifiedCharacters ν)} {f : Ω → ℂ}
  (p : ScalarPresentation Ω f) (τ : unramifiedCharacters ν)

/-- Translate the original scalar numerator and denominator on the exact
preimage of its region. -/
def translation :
    ScalarPresentation ((unramifiedParameterTranslation ν τ) ⁻¹' Ω)
      (fun χ => f (unramifiedTranslationPreimageEquiv ν τ Ω χ)) where
  numerator := unramifiedRegularTranslation ν τ p.numerator
  denominator := unramifiedRegularTranslation ν τ p.denominator
  denominator_nonzero χ := p.denominator_nonzero
    (unramifiedTranslationPreimageEquiv ν τ Ω χ)
  clears χ := p.clears (unramifiedTranslationPreimageEquiv ν τ Ω χ)

@[simp]
theorem translation_numerator :
    (p.translation τ).numerator = unramifiedRegularTranslation ν τ p.numerator := rfl

@[simp]
theorem translation_denominator :
    (p.translation τ).denominator = unramifiedRegularTranslation ν τ p.denominator := rfl

end UnramifiedOperatorFamily.ScalarPresentation

end Generic

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)

/-- The regular parameter pullback extends to the existing actual function
field; this construction has no evaluation convention at poles. -/
def rationalUnramifiedFunctionFieldTranslation
    (τ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    rationalUnramifiedFunctionField G hp hG ≃+* rationalUnramifiedFunctionField G hp hG :=
  IsFractionRing.ringEquivOfRingEquiv
    (unramifiedRegularTranslation (fun ψ => (rationalNormCharacters G ψ).toMul) τ).toRingEquiv

@[simp]
theorem rationalUnramifiedFunctionFieldTranslation_algebraMap
    (τ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    rationalUnramifiedFunctionFieldTranslation G hp hG τ
        (algebraMap
          (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
          (rationalUnramifiedFunctionField G hp hG) b) =
      algebraMap
        (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
        (rationalUnramifiedFunctionField G hp hG)
        (unramifiedRegularTranslation (fun ψ => (rationalNormCharacters G ψ).toMul) τ b) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b

/-- Complex constants are fixed, via their existing embedding in the regular
algebra and then in the actual function field. -/
theorem rationalUnramifiedFunctionFieldTranslation_constant
    (τ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) (c : ℂ) :
    rationalUnramifiedFunctionFieldTranslation G hp hG τ
        (algebraMap
          (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
          (rationalUnramifiedFunctionField G hp hG)
          (algebraMap ℂ
            (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)) c)) =
      algebraMap
        (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
        (rationalUnramifiedFunctionField G hp hG)
        (algebraMap ℂ
          (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)) c) := by
  rw [rationalUnramifiedFunctionFieldTranslation_algebraMap, AlgEquiv.commutes]

@[simp]
theorem rationalUnramifiedFunctionFieldTranslation_one :
    rationalUnramifiedFunctionFieldTranslation G hp hG 1 =
      RingEquiv.refl (rationalUnramifiedFunctionField G hp hG) := by
  unfold rationalUnramifiedFunctionFieldTranslation
  rw [unramifiedRegularTranslation_one]
  exact IsFractionRing.ringEquivOfRingEquiv_refl
    (A := unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (K := rationalUnramifiedFunctionField G hp hG)

theorem rationalUnramifiedFunctionFieldTranslation_mul
    (τ σ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    rationalUnramifiedFunctionFieldTranslation G hp hG (τ * σ) =
      (rationalUnramifiedFunctionFieldTranslation G hp hG τ).trans
        (rationalUnramifiedFunctionFieldTranslation G hp hG σ) := by
  unfold rationalUnramifiedFunctionFieldTranslation
  rw [unramifiedRegularTranslation_mul]
  exact IsFractionRing.ringEquivOfRingEquiv_comp
    (rationalUnramifiedFunctionField G hp hG)
    (rationalUnramifiedFunctionField G hp hG)
    (rationalUnramifiedFunctionField G hp hG) _ _

open UnramifiedOperatorFamily

namespace UnramifiedOperatorFamily.ScalarPresentation

variable
  {Ω : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
  {f : Ω → ℂ}

/-- The translated scalar presentation represents exactly the translated
fraction, independently of either proof of region nonemptiness. -/
theorem translation_toFunctionField
    (p : ScalarPresentation Ω f)
    (τ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hΩ : Ω.Nonempty)
    (hΩτ : ((unramifiedParameterTranslation
      (fun ψ => (rationalNormCharacters G ψ).toMul) τ) ⁻¹' Ω).Nonempty) :
    (p.translation τ).toFunctionField G hp hG hΩτ =
      rationalUnramifiedFunctionFieldTranslation G hp hG τ
        (p.toFunctionField G hp hG hΩ) := by
  rw [toFunctionField_eq_div, toFunctionField_eq_div, map_div₀,
    rationalUnramifiedFunctionFieldTranslation_algebraMap,
    rationalUnramifiedFunctionFieldTranslation_algebraMap]
  rfl

end UnramifiedOperatorFamily.ScalarPresentation

variable
  {Ω D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Scalar extraction from the pulled-back actual rational operator family
commutes with function-field translation. The translated rationality proof
may be chosen independently. Scalarity and normalization are unnecessary. -/
theorem rationalUnramifiedOperatorScalar_translation
    (τ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))
    (A : Ω → Module.End ℂ V) (hA : IsRationalOperatorOn Ω A)
    (hAτ : IsRationalOperatorOn
      ((unramifiedParameterTranslation (fun ψ => (rationalNormCharacters G ψ).toMul) τ) ⁻¹' Ω)
      (fun χ => A (unramifiedTranslationPreimageEquiv
        (fun ψ => (rationalNormCharacters G ψ).toMul) τ Ω χ)))
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hΩ : Ω.Nonempty)
    (hΩτ : ((unramifiedParameterTranslation
      (fun ψ => (rationalNormCharacters G ψ).toMul) τ) ⁻¹' Ω).Nonempty)
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω) :
    rationalUnramifiedOperatorScalar G hp hG
        (fun χ => A (unramifiedTranslationPreimageEquiv
          (fun ψ => (rationalNormCharacters G ψ).toMul) τ Ω χ))
        hAτ v ℓ hΩτ =
      rationalUnramifiedFunctionFieldTranslation G hp hG τ
        (rationalUnramifiedOperatorScalar G hp hG A hA v ℓ hΩ) := by
  let p := scalarCoefficientPresentation A hA v ℓ
  let e := unramifiedParameterTranslation (fun ψ => (rationalNormCharacters G ψ).toMul) τ
  have hpre : (e ⁻¹' D).Nonempty := by
    obtain ⟨χ, hχ⟩ := hne
    exact ⟨e.symm χ, by simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply]⟩
  rw [rationalUnramifiedOperatorScalar_eq_presentation G hp hG _ _ _ _
    (p.translation τ) hΩτ (hD.preimage e.continuous) hpre
    (fun _ hχ => hDΩ hχ)]
  exact p.translation_toFunctionField G hp hG τ hΩ hΩτ

end ActualCharacters

end Langlands.Plancherel
