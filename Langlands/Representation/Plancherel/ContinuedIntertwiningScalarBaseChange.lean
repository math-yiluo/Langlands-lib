import Langlands.Representation.Plancherel.ContinuedIntertwiningScalarNaturality
import Langlands.Representation.Plancherel.ContinuedIntertwiningBaseChange
import Langlands.Representation.Plancherel.UnramifiedScalarTranslation

/-! # Translation of composite scalars under a change of orbit base -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uI uV uW uV' uW'

namespace UnramifiedOperatorFamily.RationalOperatorContinuationData

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {I : Type uI} {ν : I → (H →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
  {Ω Λ : Set (unramifiedCharacters ν)}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}

/-- Continue the family in a new parameter chart and new source and target
carriers, with the exact pulled-back whole-operator denominator. -/
def baseChange (p : RationalOperatorContinuationData Ω A)
    (τ : unramifiedCharacters ν) (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W') :
    RationalOperatorContinuationData ((unramifiedParameterTranslation ν τ) ⁻¹' Ω)
      (fun χ => T.toLinearMap.comp
        ((A (unramifiedTranslationPreimageEquiv ν τ Ω χ)).comp S.symm.toLinearMap)) :=
  (p.translation τ).congr S T

@[simp]
theorem baseChange_regularRegion (p : RationalOperatorContinuationData Ω A)
    (τ : unramifiedCharacters ν) (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W') :
    (p.baseChange τ S T).regularRegion =
      (unramifiedParameterTranslation ν τ) ⁻¹' p.regularRegion := rfl

theorem baseChange_continuedOperator (p : RationalOperatorContinuationData Ω A)
    (τ : unramifiedCharacters ν) (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W')
    (χ : (p.baseChange τ S T).regularRegion) :
    (p.baseChange τ S T).continuedOperator χ =
      T.toLinearMap.comp
        ((p.continuedOperator ⟨τ * χ.val, χ.property⟩).comp S.symm.toLinearMap) :=
  (p.translation τ).congr_continuedOperator S T χ

/-- Translation of the continued composite is exactly pullback of the
original composite, with no extra restriction on its regular region. -/
theorem translation_continuedComposite
    (p : RationalOperatorContinuationData Ω A)
    (q : RationalOperatorContinuationData Λ B) (τ : unramifiedCharacters ν)
    (χ : ↥((p.translation τ).regularRegion ∩ (q.translation τ).regularRegion)) :
    (p.translation τ).continuedComposite (q.translation τ) χ =
      p.continuedComposite q ⟨τ * χ.val, χ.property⟩ := rfl

/-- The intermediate carrier equivalence cancels after base change. -/
theorem baseChange_continuedComposite
    (p : RationalOperatorContinuationData Ω A)
    (q : RationalOperatorContinuationData Λ B)
    (τ : unramifiedCharacters ν) (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W')
    (χ : ↥((p.baseChange τ S T).regularRegion ∩
      (q.baseChange τ T S).regularRegion)) (v : V) :
    (p.baseChange τ S T).continuedComposite (q.baseChange τ T S) χ (S v) =
      S (p.continuedComposite q ⟨τ * χ.val, χ.property⟩ v) :=
  (p.translation τ).continuedComposite_congr (q.translation τ) S T χ v

end UnramifiedOperatorFamily.RationalOperatorContinuationData

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
  {Ω Λ Ω' Λ' D E :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}
  {A' : Ω' → V' →ₗ[ℂ] W'} {B' : Λ' → W' →ₗ[ℂ] V'}
  (p : RationalOperatorContinuationData Ω A)
  (q : RationalOperatorContinuationData Λ B)
  (τ : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))

include hp hL

/-- Extraction of a continued composite coefficient commutes with
translation in the actual unramified function field, without scalarity. -/
theorem continuedCompositeRationalScalar_translation
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty)
    (hΩτ : ((unramifiedParameterTranslation _ τ) ⁻¹' Ω).Nonempty)
    (hΛτ : ((unramifiedParameterTranslation _ τ) ⁻¹' Λ).Nonempty)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    continuedCompositeRationalScalar L hp hL (p.translation τ) (q.translation τ)
        hΩτ hΛτ v ℓ =
      rationalUnramifiedFunctionFieldTranslation L hp hL τ
        (continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ) := by
  exact rationalUnramifiedOperatorScalar_translation L hp hL τ
    (p.continuedComposite q) (p.continuedComposite_rational q)
    ((p.translation τ).continuedComposite_rational (q.translation τ)) v ℓ
    (continuedCompositeRegion_nonempty L hp hL p q hΩ hΛ)
    (continuedCompositeRegion_nonempty L hp hL (p.translation τ) (q.translation τ) hΩτ hΛτ)
    (p.regularRegion_isOpen.inter q.regularRegion_isOpen)
    (continuedCompositeRegion_nonempty L hp hL p q hΩ hΛ) Set.Subset.rfl

/-- The constructed base-change data preserve coefficients when the
extraction pair is transported, and translate their function-field value. -/
theorem continuedCompositeRationalScalar_baseChange
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty)
    (hΩτ : ((unramifiedParameterTranslation _ τ) ⁻¹' Ω).Nonempty)
    (hΛτ : ((unramifiedParameterTranslation _ τ) ⁻¹' Λ).Nonempty)
    (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W')
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    continuedCompositeRationalScalar L hp hL
        (p.baseChange τ S T) (q.baseChange τ T S) hΩτ hΛτ
        (S v) (ℓ.comp S.symm.toLinearMap) =
      rationalUnramifiedFunctionFieldTranslation L hp hL τ
        (continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ) := by
  exact (continuedCompositeRationalScalar_congr L hp hL
    (p.translation τ) (q.translation τ) hΩτ hΛτ S T v ℓ).trans
      (continuedCompositeRationalScalar_translation L hp hL p q τ hΩ hΛ hΩτ hΛτ v ℓ)

variable
  (p' : RationalOperatorContinuationData Ω' A')
  (q' : RationalOperatorContinuationData Λ' B')
  (S : V ≃ₗ[ℂ] V') (T : W ≃ₗ[ℂ] W')
  (hD : IsOpen D) (hneD : D.Nonempty)
  (hDΩ : D ⊆ (unramifiedParameterTranslation _ τ) ⁻¹' Ω) (hDΩ' : D ⊆ Ω')
  (hE : IsOpen E) (hneE : E.Nonempty)
  (hEΛ : E ⊆ (unramifiedParameterTranslation _ τ) ⁻¹' Λ) (hEΛ' : E ⊆ Λ')
  (hnatA : ∀ χ (hχ : χ ∈ D),
    (A' ⟨χ, hDΩ' hχ⟩).comp S.toLinearMap =
      T.toLinearMap.comp (A ⟨τ * χ, hDΩ hχ⟩))
  (hnatB : ∀ χ (hχ : χ ∈ E),
    (B' ⟨χ, hEΛ' hχ⟩).comp T.toLinearMap =
      S.toLinearMap.comp (B ⟨τ * χ, hEΛ hχ⟩))

set_option quotPrecheck false in
local notation "hΩ" => (hneD.image (unramifiedParameterTranslation _ τ)).mono
  (Set.image_subset_iff.mpr hDΩ)
set_option quotPrecheck false in
local notation "hΛ" => (hneE.image (unramifiedParameterTranslation _ τ)).mono
  (Set.image_subset_iff.mpr hEΛ)

include hD hneD hDΩ hDΩ' hE hneE hEΛ hEΛ' hnatA hnatB

/-- Independent continuation choices satisfy the translated composite
square, with separate original open sets for its two factors. -/
theorem continuedComposite_translation_natural
    (χ : ↥(((unramifiedParameterTranslation _ τ) ⁻¹'
      (p.regularRegion ∩ q.regularRegion)) ∩
        (p'.regularRegion ∩ q'.regularRegion))) (v : V) :
    p'.continuedComposite q' ⟨χ.val, χ.property.2⟩ (S v) =
      S (p.continuedComposite q ⟨τ * χ.val, χ.property.1⟩ v) :=
  continuedComposite_natural L hp hL (p.translation τ) (q.translation τ) p' q'
    S T hD hneD hDΩ hDΩ' hE hneE hEΛ hEΛ' hnatA hnatB χ v

/-- For independent original families and continuation choices, a change
of base translates the coefficient fraction with its transported pair. -/
theorem continuedCompositeRationalScalar_translation_natural
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    continuedCompositeRationalScalar L hp hL p' q'
        (hneD.mono hDΩ') (hneE.mono hEΛ') (S v) (ℓ.comp S.symm.toLinearMap) =
      rationalUnramifiedFunctionFieldTranslation L hp hL τ
        (continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ) := by
  exact (continuedCompositeRationalScalar_natural L hp hL
    (p.translation τ) (q.translation τ) p' q' S T
    hD hneD hDΩ hDΩ' hE hneE hEΛ hEΛ' hnatA hnatB v ℓ).symm.trans
      (continuedCompositeRationalScalar_translation L hp hL p q τ hΩ hΛ
        (hneD.mono hDΩ) (hneE.mono hEΛ) v ℓ)

/-- Generic scalarity on the original chart makes the translated scalar
independent of all four continuations and both normalized extraction pairs. -/
theorem continuedCompositeRationalScalar_base_independent
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hU : IsOpen U) (hneU : U.Nonempty)
    (hscalar : ∀ χ : ↥(p.regularRegion ∩ q.regularRegion), χ.val ∈ U →
      ∃ c : ℂ, p.continuedComposite q χ = c • LinearMap.id)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (w : V') (m : V' →ₗ[ℂ] ℂ) (hm : m w = 1) :
    continuedCompositeRationalScalar L hp hL p' q'
        (hneD.mono hDΩ') (hneE.mono hEΛ') w m =
      rationalUnramifiedFunctionFieldTranslation L hp hL τ
        (continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ) := by
  let t := unramifiedParameterTranslation (fun ψ => (rationalNormCharacters L ψ).toMul) τ
  have hne : (t ⁻¹' U).Nonempty := by
    obtain ⟨χ, hχ⟩ := hneU
    exact ⟨t.symm χ, by simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply]⟩
  have he := continuedCompositeRationalScalar_representative_independent L hp hL
    (p.translation τ) (q.translation τ) p' q' S T
    hD hneD hDΩ hDΩ' hE hneE hEΛ hEΛ' hnatA hnatB
    (hU.preimage t.continuous) hne
    (fun χ hχ => hscalar ⟨τ * χ.val, χ.property⟩ hχ)
    v ℓ hℓ w m hm
  exact he.symm.trans
    (continuedCompositeRationalScalar_translation L hp hL p q τ hΩ hΛ
      (hneD.mono hDΩ) (hneE.mono hEΛ) v ℓ)

end ActualCharacters

section ActualInduction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ M U₀ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection) (hr₁ : Continuous h₁.projection)
  (e : GroupScheme.rationalPoints L ≃ₜ* M)
  (hν : ∀ ψ, Continuous (rationalNormCharacters L ψ).toMul)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (B : Langlands.SmoothRep.{0, uG, uW} ℂ M)
  {Ω₁₀ Ω₀₁ Ω₁₀' Ω₀₁' D₁₀ D₀₁ :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}

local notation "νL" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "νM" => (fun ψ => MonoidHom.comp
  (Additive.toMul (rationalNormCharacters L ψ)) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e νL
set_option quotPrecheck false in
local notation "hνM" => (fun ψ => (hν ψ).comp e.symm.continuous)

variable
  (τ : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
  (J₁₀ : ∀ χ : Ω₁₀,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)
  (J₀₁ : ∀ χ : Ω₀₁,
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation.IntertwiningMap
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A).representation)
  (p : RationalOperatorContinuationData Ω₁₀ (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (J₁₀ χ)))
  (q : RationalOperatorContinuationData Ω₀₁ (fun χ =>
    compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      A (J₀₁ χ)))
  (J₁₀' : ∀ χ : Ω₁₀',
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B).representation.IntertwiningMap
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B).representation)
  (J₀₁' : ∀ χ : Ω₀₁',
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B).representation.IntertwiningMap
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B).representation)
  (p' : RationalOperatorContinuationData Ω₁₀' (fun χ =>
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B (J₁₀' χ)))
  (q' : RationalOperatorContinuationData Ω₀₁' (fun χ =>
    compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
      B (J₀₁' χ)))
  (hD₁₀ : IsOpen D₁₀) (hne₁₀ : D₁₀.Nonempty)
  (hD₁₀Ω : D₁₀ ⊆ (unramifiedParameterTranslation
    (fun ψ => (rationalNormCharacters L ψ).toMul) τ) ⁻¹' Ω₁₀) (hD₁₀Ω' : D₁₀ ⊆ Ω₁₀')
  (hD₀₁ : IsOpen D₀₁) (hne₀₁ : D₀₁.Nonempty)
  (hD₀₁Ω : D₀₁ ⊆ (unramifiedParameterTranslation
    (fun ψ => (rationalNormCharacters L ψ).toMul) τ) ⁻¹' Ω₀₁) (hD₀₁Ω' : D₀₁ ⊆ Ω₀₁')
  (a : (A.twist
    (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
      τ).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        τ))).representation.Equiv B.representation)
  (hnat₁₀ : ∀ χ (hχ : χ ∈ D₁₀)
    (f : UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        (τ * χ)) A),
    J₁₀' ⟨χ, hD₁₀Ω' hχ⟩
        (inducedMap h₀ hU₀
          (transportedBaseTwistEquiv e (fun ψ => (rationalNormCharacters L ψ).toMul)
            τ χ a).toIntertwiningMap
          f) =
      inducedMap h₁ hU₁
        (transportedBaseTwistEquiv e (fun ψ => (rationalNormCharacters L ψ).toMul)
          τ χ a).toIntertwiningMap
        (J₁₀ ⟨τ * χ, hD₁₀Ω hχ⟩ f))
  (hnat₀₁ : ∀ χ (hχ : χ ∈ D₀₁)
    (f : UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        (τ * χ)) A),
    J₀₁' ⟨χ, hD₀₁Ω' hχ⟩
        (inducedMap h₁ hU₁
          (transportedBaseTwistEquiv e (fun ψ => (rationalNormCharacters L ψ).toMul)
            τ χ a).toIntertwiningMap
          f) =
      inducedMap h₀ hU₀
        (transportedBaseTwistEquiv e (fun ψ => (rationalNormCharacters L ψ).toMul)
          τ χ a).toIntertwiningMap
        (J₀₁ ⟨τ * χ, hD₀₁Ω hχ⟩ f))

local notation "C₀" => compactInductionBaseChangeEquiv h₀ K hP₀ hK νM hνM hr₀ (χM τ) a
local notation "C₁" => compactInductionBaseChangeEquiv h₁ K hP₁ hK νM hνM hr₁ (χM τ) a
set_option quotPrecheck false in
local notation "hΩ₁₀" => (hne₁₀.image (unramifiedParameterTranslation νL τ)).mono
  (Set.image_subset_iff.mpr hD₁₀Ω)
set_option quotPrecheck false in
local notation "hΩ₀₁" => (hne₀₁.image (unramifiedParameterTranslation νL τ)).mono
  (Set.image_subset_iff.mpr hD₀₁Ω)

include hp hL hD₁₀ hne₁₀ hD₁₀Ω hD₁₀Ω' hD₀₁ hne₀₁ hD₀₁Ω hD₀₁Ω' hnat₁₀ hnat₀₁

/-- The scalar extracted from independently continued actual induction
intertwiners transforms by the actual character translation when the base
representation changes from A to an equivalent twist B. Generic induced
irreducibility is required only for A on one nonempty ambient open set. -/
theorem continuedInductionCompositeRationalScalar_base_independent
    [TopologicalSpace.SeparableSpace G]
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hU : IsOpen U) (hneU : U.Nonempty)
    (hi : ∀ χ ∈ U,
      (UnramifiedLeviInduction h₀ hU₀ νM (χM χ) A).IsIrreducible)
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (w : CompactInductionPicture h₀ K B)
    (m : CompactInductionPicture h₀ K B →ₗ[ℂ] ℂ) (hm : m w = 1) :
    continuedCompositeRationalScalar L hp hL p' q'
        (hne₁₀.mono hD₁₀Ω') (hne₀₁.mono hD₀₁Ω') w m =
      rationalUnramifiedFunctionFieldTranslation L hp hL τ
        (continuedCompositeRationalScalar L hp hL p q hΩ₁₀ hΩ₀₁ v ℓ) := by
  refine continuedCompositeRationalScalar_base_independent L hp hL
    p q τ p' q' (C₀).toLinearEquiv (C₁).toLinearEquiv
    hD₁₀ hne₁₀ hD₁₀Ω hD₁₀Ω' hD₀₁ hne₀₁ hD₀₁Ω hD₀₁Ω'
    ?_ ?_ hU hneU ?_ v ℓ hℓ w m hm
  · intro χ hχ
    apply LinearMap.ext
    intro z
    exact ((compactIntertwiningOperator_transportedBaseChange_iff
      e νL h₀ hU₀ hδ₀ K hP₀ hK hP₀K hν hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ τ χ a
      (J₁₀ ⟨τ * χ, hD₁₀Ω hχ⟩) (J₁₀' ⟨χ, hD₁₀Ω' hχ⟩)).mp (hnat₁₀ χ hχ)) z
  · intro χ hχ
    apply LinearMap.ext
    intro z
    exact ((compactIntertwiningOperator_transportedBaseChange_iff
      e νL h₁ hU₁ hδ₁ K hP₁ hK hP₁K hν hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ τ χ a
      (J₀₁ ⟨τ * χ, hD₀₁Ω hχ⟩) (J₀₁' ⟨χ, hD₀₁Ω' hχ⟩)).mp (hnat₀₁ χ hχ)) z
  · intro χ hχ
    exact continuedInductionComposite_generic_scalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      J₁₀ J₀₁ p q
      ((unramifiedParameterTranslation νL τ).isOpenMap D₁₀ hD₁₀)
      (hne₁₀.image (unramifiedParameterTranslation νL τ))
      (Set.image_subset_iff.mpr hD₁₀Ω)
      ((unramifiedParameterTranslation νL τ).isOpenMap D₀₁ hD₀₁)
      (hne₀₁.image (unramifiedParameterTranslation νL τ))
      (Set.image_subset_iff.mpr hD₀₁Ω) hi ⟨χ.val, hχ, χ.property⟩

end ActualInduction

end Langlands.Plancherel
