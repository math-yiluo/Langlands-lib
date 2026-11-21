import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerIntertwiner

/-! # Mixed smooth realization of the actual Whittaker values -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 65000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic
  Langlands.Global.ArchimedeanGL
  NumberField MeasureTheory Langlands.Archimedean Langlands.Archimedean.MixedSmooth

universe u v

attribute [local instance] regSchemeAffine regSchemeSmooth regRationalAddCommGroup
  regContinuousAddCommGroup regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup
  regRealizationAddCommGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
  (hcomm : ∀ g d x, π g (σ d x) = σ d (π g x))

local notation "W" => Vectors (A := ArchimedeanMatrix F (r + 1)) σ π hcomm

/-- An actual translated-value realization of a mixed Whittaker functional. -/
def HasMixedWhittakerModel (j : T.Space →ₗ[ℂ] W) : Prop :=
  ∃ ℓ : W →ₗ[ℂ] ℂ, IsMixedWhittakerFunctional (r := r) ψ σ π hcomm ℓ ∧
    (∀ (v : T.Space) (a : ArchimedeanGL F (r + 1)) (d : FiniteAdelicGL F (r + 1)),
      ℓ (MixedSmooth.finiteRepresentation σ π hcomm d
        (MixedSmooth.archimedeanRepresentation σ π hcomm a (j v))) =
        cuspWhittaker F T ψ v (adelicPoint F (r + 1) a d)) ∧
    (∀ v : T.Space, v ≠ 0 → ℓ ≠ 0)

/-- The remaining uniqueness assertion on the supplied mixed smooth
representation, using the same continuity and adelic character. -/
def MixedWhittakerUniqueness : Prop :=
  ∀ ℓ₀ ℓ₁ : W →ₗ[ℂ] ℂ,
    IsMixedWhittakerFunctional (r := r) ψ σ π hcomm ℓ₀ →
    IsMixedWhittakerFunctional (r := r) ψ σ π hcomm ℓ₁ →
    ℓ₀ ≠ 0 → ∃ s : ℂ, ℓ₁ = s • ℓ₀

universe v'

variable {E' : Type v'} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  (σ' : FiniteAdelicGL F (r + 1) →* (E' →L[ℂ] E'))
  (π' : ArchimedeanGL F (r + 1) →* (E' →L[ℂ] E'))
  (c' : ∀ g d x, π' g (σ' d x) = σ' d (π' g x))
  (N : E →L[ℂ] E') (hF : ∀ d x, N (σ d x) = σ' d (N x))
  (hA : ∀ g x, N (π g x) = π' g (N x))

local notation "W'" => Vectors (A := ArchimedeanMatrix F (r + 1)) σ' π' c'
local notation "P" => MixedSmooth.map (A := ArchimedeanMatrix F (r + 1)) σ π hcomm σ' π' c' N hF hA

/-- Mixed Whittaker uniqueness and the bounded extension of the original
map give one scalar for every actual original coefficient. -/
theorem exists_proportional_whittaker_of_mixed_models
    (T' : CuspidalOperatorRealization F r)
    (e : T.Space →ₗ[ℂ] T'.Space)
    (j : T.Space →ₗ[ℂ] W) (j' : T'.Space →ₗ[ℂ] W')
    (he : ∀ v, P (j v) = j' (e v))
    (hm : HasMixedWhittakerModel T ψ σ π hcomm j)
    (hm' : HasMixedWhittakerModel T' ψ σ' π' c' j')
    (huniq : MixedWhittakerUniqueness (r := r) ψ σ π hcomm) :
    ∃ s : ℂ, ∀ (v : T.Space) (g : Points F (r + 1)),
      cuspWhittaker F T' ψ (e v) g = s * cuspWhittaker F T ψ v g := by
  obtain ⟨ℓ, hℓ, hval, hnonzero⟩ := hm
  obtain ⟨ℓ', hℓ', hval', _⟩ := hm'
  have hnontrivial := @exists_ne T.Space T.space_nontrivial (0 : T.Space)
  obtain ⟨v, hv⟩ := hnontrivial
  have hc := isMixedWhittakerFunctional_comp (r := r) (E := E) (E' := E') ψ
    σ π hcomm σ' π' c' N hF hA ℓ' hℓ'
  let ℓ₁ := ℓ'.comp (P).toLinearMap
  have heq := huniq ℓ ℓ₁ hℓ hc (hnonzero v hv)
  obtain ⟨s, hs⟩ := heq
  have hvalues := cuspWhittaker_eq_of_mixed_functional (E := E) (E' := E') ψ σ π hcomm σ' π' c' N hF hA
    T T' e j j' he ℓ ℓ' hval hval' s hs
  exact ⟨s, hvalues⟩

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
