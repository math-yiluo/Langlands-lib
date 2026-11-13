import Langlands.LocalFactor.BrauerKernel.RealizationCharacter
import Langlands.LocalFactor.BrauerKernel.GeneratorTransport

/-! # Generator values at the distinguished place of a global realization -/

noncomputable section

set_option autoImplicit false

universe uF uA uE

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CommonClosure Correspondence
open Langlands.Global.CompletionPadic Weil.Local

section Trace

variable {p : ℕ} [Fact p.Prime] (A : PadicField.{uA} p) (F : PadicField.{uF} p)
  (E : PadicField.{uE} p)

/-- Trace characters are compatible with an isomorphism of the base: for `φ' : A ≃ F` and an
embedding `g : A → E`, the trace character on `E` of the transport of `ψA` along `φ'`, for the
embedding `g ∘ φ'⁻¹`, is the trace character of `ψA` for `g`. -/
theorem embeddingTraceCharacter_comp_symm (φ' : A.Carrier ≃ₐ[Padic p] F.Carrier)
    (g : A.Carrier →ₐ[Padic p] E.Carrier) (ψA : NontrivialAdditiveCharacter A) :
    embeddingTraceCharacter F E (g.comp φ'.symm.toAlgHom)
        (PadicField.ConductorTransport.additiveCharacter A F φ' ψA) =
      embeddingTraceCharacter A E g ψA := by
  let := E.canonicalTopologicalData.topology
  apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
  intro x
  let : Algebra F.Carrier E.Carrier := extensionAlgebra F E (g.comp φ'.symm.toAlgHom)
  let : Algebra A.Carrier E.Carrier := extensionAlgebra A E g
  change ψA (φ'.symm (Algebra.trace F.Carrier E.Carrier x)) =
    ψA (Algebra.trace A.Carrier E.Carrier x)
  congr 1
  have he : (algebraMap F.Carrier E.Carrier).comp (φ'.toRingEquiv : A.Carrier →+* F.Carrier) =
      (RingEquiv.refl E.Carrier : E.Carrier →+* E.Carrier).comp
        (algebraMap A.Carrier E.Carrier) := by
    ext a
    change g (φ'.symm (φ' a)) = g a
    rw [AlgEquiv.symm_apply_apply]
  have ht := Algebra.trace_eq_of_equiv_equiv φ'.toRingEquiv (RingEquiv.refl E.Carrier) he x
  exact ht.symm

end Trace

section Place

open ClassField.Global ClassField.Global.RelativeWeilGroup

variable {k K' : Type} [Field k] [Field K'] [NumberField k] [NumberField K'] [Algebra k K']
  (v : HeightOneSpectrum (𝓞 k)) {F : PadicField.{uF} (residuePrime v)} (K : Extension F)
  [Normal F.Carrier K.field] (θ : (K' ≃ₐ[k] K') ≃* (K.field ≃ₐ[F.Carrier] K.field))
  (w : HeightOneSpectrum (𝓞 K')) [w.asIdeal.LiesOver v.asIdeal]
  (φ : v.adicCompletion k ≃+* F.Carrier) (ψ : w.adicCompletion K' ≃+* K.field)
  (hφ : @Continuous _ _ _ F.canonicalTopology φ)
  (hφ' : @Continuous _ _ F.canonicalTopology _ φ.symm)
  (hψ : @Continuous _ _ _ (K.asPadicField (p := residuePrime v)).canonicalTopology ψ)
  (hcomp : ∀ x : k, ψ (algebraMap K' (w.adicCompletion K') (algebraMap k K' x)) =
    algebraMap F.Carrier K.field (φ (algebraMap k (v.adicCompletion k) x)))
  (hθ : ∀ σ x, θ σ (ψ (algebraMap K' (w.adicCompletion K') x)) =
    ψ (algebraMap K' (w.adicCompletion K') (σ x)))

/-- The continuous isomorphism `φ : k_v ≃ F` as an isomorphism of `ℚ_p`-algebras. -/
def realizationPadicEquiv :
    letI := (padicField v).algebra
    (padicField v).Carrier ≃ₐ[Padic (residuePrime v)] F.Carrier :=
  letI := (padicField v).algebra
  AlgEquiv.ofRingEquiv (f := φ) (realization_padicMap v φ hφ)

theorem realizationPadicEquiv_apply (x : v.adicCompletion k) :
    realizationPadicEquiv v φ hφ x = φ x :=
  rfl

include hφ' in
/-- **Generator values at the distinguished place.** Let `g` be a generator over the bottom field
whose field `L` lies in `K`, and `u` the place of the global field of `L` under `w`. If the two
characters of `g` are the transports along the generator-field isomorphism of quasicharacters
`η₁`, `η₂` of `𝕃_u`, then for the base character of the transport of `ψv` along `φ` the generator
value is `ε(η₁, ψv ∘ Tr, μ, 0) / ε(η₂, ψv ∘ Tr, μ, 0)` on `𝕃_u`, for every Haar measure `μ`. -/
theorem generatorValue_eq_realizationEpsilon (g : Generator F (baseExtension F))
    (hL : g.extension.field ≤ K.field)
    (u : HeightOneSpectrum (𝓞 (realizationSubfield K θ g.extension)))
    [w.asIdeal.LiesOver u.asIdeal] [u.asIdeal.LiesOver v.asIdeal]
    (η₁ η₂ : QuasiCharacter (towerPadicField v u))
    (h₁ : g.first = PadicField.ConductorTransport.quasicharacter (towerPadicField v u)
      (g.extension.asPadicField (p := residuePrime v))
      (realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ g.extension hL u) η₁)
    (h₂ : g.second = PadicField.ConductorTransport.quasicharacter (towerPadicField v u)
      (g.extension.asPadicField (p := residuePrime v))
      (realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ g.extension hL u) η₂)
    (ψv : NontrivialAdditiveCharacter (padicField v))
    (ψb : AdditiveCharacter F (baseExtension F))
    (hψb : IsBaseCharacter F (PadicField.ConductorTransport.additiveCharacter (padicField v) F
      (realizationPadicEquiv v φ hφ) ψv) ψb)
    (measures : HaarFamily F) (μE : LocalAdditiveHaarMeasure (towerPadicField v u)) :
    (generatorValue F (baseExtension F) ψb measures g : ℂ) =
      PadicAbelian.epsilon (towerPadicField v u).canonicalTopologicalData η₁
          (SystemEpsilon.standaloneTraceCharacter (padicField v) (towerPadicField v u)
            (RelativeWeilGroup.completionPadicAlgHom v u) ψv)
          (@HarmonicAnalysis.AdditiveHaarMeasure.measure _ _
            (towerPadicField v u).canonicalTopologicalData.topology
            (@borel _ (towerPadicField v u).canonicalTopologicalData.topology) μE) 0 /
        PadicAbelian.epsilon (towerPadicField v u).canonicalTopologicalData η₂
          (SystemEpsilon.standaloneTraceCharacter (padicField v) (towerPadicField v u)
            (RelativeWeilGroup.completionPadicAlgHom v u) ψv)
          (@HarmonicAnalysis.AdditiveHaarMeasure.measure _ _
            (towerPadicField v u).canonicalTopologicalData.topology
            (@borel _ (towerPadicField v u).canonicalTopologicalData.topology) μE) 0 := by
  let := (padicField v).algebra
  let := (towerPadicField v u).algebra
  have hf : realizationBaseAlgHom v u φ hφ' =
      (RelativeWeilGroup.completionPadicAlgHom v u).comp
        (realizationPadicEquiv v φ hφ).symm.toAlgHom :=
    AlgHom.ext fun _ => rfl
  have h := generatorValue_eq_epsilon_of_algEquiv F (towerPadicField v u)
    (realizationBaseAlgHom v u φ hφ') g
    (realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ g.extension hL u)
    (realizationGeneratorEquiv_base v K θ w φ ψ hφ hφ' hψ hcomp hθ g.extension hL u) η₁ η₂ h₁ h₂
    (PadicField.ConductorTransport.additiveCharacter (padicField v) F
      (realizationPadicEquiv v φ hφ) ψv) ψb hψb measures μE
  rw [hf, embeddingTraceCharacter_comp_symm] at h
  exact h

end Place

end Langlands.LocalFactor.NonabelianBrauer
