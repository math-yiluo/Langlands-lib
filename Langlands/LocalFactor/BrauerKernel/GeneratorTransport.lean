import Langlands.LocalFactor.BrauerKernel.StandaloneBridge

/-! # Generator values on an isomorphic standalone field -/

noncomputable section

set_option autoImplicit false

universe uF uE

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The trace character `ψF ∘ Tr_{E/F}` on a standalone extension `E` of `F` given by an
embedding `f`, with independent field universes. -/
def embeddingTraceCharacter (ψF : NontrivialAdditiveCharacter F) :
    NontrivialAdditiveCharacter E :=
  letI := Weil.Local.extensionAlgebra F E f
  haveI := Weil.Local.extensionAlgebra_isScalarTower F E f
  F.canonicalTopologicalData.traceCharacter E.canonicalTopologicalData ψF

section Transport

/-- The `ℚ_p`-algebra structure of a finite intermediate field in the common closure is the
one of its standalone repackaging. -/
local instance generatorTransportAlgebra (L : Extension F) : Algebra (Padic p) L.field :=
  (L.asPadicField (p := p)).algebra

variable (L : Extension F)
  (σ : E.Carrier ≃ₐ[Padic p] (L.asPadicField (p := p)).Carrier)

/-- If `σ : E ≃ L` lies over `F` (that is, `σ ∘ f` is the inclusion of `F` in the common
closure), the trace from `L` to the bottom field corresponds to the trace of `E / F`. -/
theorem botEquiv_trace_eq_of_algEquiv
    (hσ : ∀ a : F.Carrier, ((σ (f a) : L.field) : AlgebraicClosure F.Carrier) =
      algebraMap F.Carrier (AlgebraicClosure F.Carrier) a)
    (h : (baseExtension F).field ≤ L.field) (y : L.field) :
    IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)
        (@Algebra.trace (baseExtension F).field L.field _ _
          (IntermediateField.inclusion h).toAlgebra y) =
      @Algebra.trace F.Carrier E.Carrier _ _ (Weil.Local.extensionAlgebra F E f)
        (σ.symm y) := by
  let := Weil.Local.extensionAlgebra F E f
  let : Algebra (baseExtension F).field L.field := (IntermediateField.inclusion h).toAlgebra
  let e₁ : F.Carrier ≃+* (baseExtension F).field :=
    (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).symm.toRingEquiv
  let e₂ : E.Carrier ≃+* L.field := σ.toRingEquiv
  have he : (algebraMap (baseExtension F).field L.field).comp (e₁ : F.Carrier →+* _) =
      (e₂ : E.Carrier →+* _).comp (algebraMap F.Carrier E.Carrier) := by
    ext a
    exact (hσ a).symm
  have ht := Algebra.trace_eq_of_equiv_equiv e₁ e₂ he (e₂.symm y)
  rw [RingEquiv.apply_symm_apply] at ht
  exact ht.symm

/-- Under the same hypothesis, the bottom-field trace character of a base additive character
of `ψF` is the transport along `σ` of `ψF ∘ Tr_{E/F}`. -/
theorem traceCharacter_eq_additiveCharacter_of_algEquiv
    (hσ : ∀ a : F.Carrier, ((σ (f a) : L.field) : AlgebraicClosure F.Carrier) =
      algebraMap F.Carrier (AlgebraicClosure F.Carrier) a)
    (h : (baseExtension F).field ≤ L.field) (ψF : NontrivialAdditiveCharacter F)
    (ψ : AdditiveCharacter F (baseExtension F)) (hψ : IsBaseCharacter F ψF ψ) :
    traceCharacter F (baseExtension F) L h ψ =
      PadicField.ConductorTransport.additiveCharacter E (L.asPadicField (p := p)) σ
        (embeddingTraceCharacter F E f ψF) := by
  let := F.canonicalTopologicalData.topology
  let := (fieldData F L).topology
  apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
  intro y
  change ψ _ = ψF _
  rw [hψ]
  exact congrArg ψF.toAddChar (botEquiv_trace_eq_of_algEquiv F E f L σ hσ h y)

local instance generatorTransportTopology : TopologicalSpace E.Carrier :=
  E.canonicalTopologicalData.topology

local instance generatorTransportMeasurable : MeasurableSpace E.Carrier := borel E.Carrier

/-- **Generator values through a field isomorphism.** Let `g` be a generator over the bottom
field with field `L`, and let `σ : E ≃ L` be a `ℚ_p`-isomorphism from a standalone extension
`f : F → E` lying over `F`. If the two characters of `g` are the transports along `σ` of
quasicharacters `η`, `η'` of `E`, then the generator value for the base character of `ψF`
is `ε(η, ψF ∘ Tr_{E/F}, μE, 0) / ε(η', ψF ∘ Tr_{E/F}, μE, 0)`, for any Haar measure `μE`. -/
theorem generatorValue_eq_epsilon_of_algEquiv (g : Generator F (baseExtension F))
    (σ : E.Carrier ≃ₐ[Padic p] (g.extension.asPadicField (p := p)).Carrier)
    (hσ : ∀ a : F.Carrier, ((σ (f a) : g.extension.field) : AlgebraicClosure F.Carrier) =
      algebraMap F.Carrier (AlgebraicClosure F.Carrier) a)
    (η η' : QuasiCharacter E)
    (hη : g.first = PadicField.ConductorTransport.quasicharacter E
      (g.extension.asPadicField (p := p)) σ η)
    (hη' : g.second = PadicField.ConductorTransport.quasicharacter E
      (g.extension.asPadicField (p := p)) σ η')
    (ψF : NontrivialAdditiveCharacter F) (ψ : AdditiveCharacter F (baseExtension F))
    (hψ : IsBaseCharacter F ψF ψ) (measures : HaarFamily F) (μE : LocalAdditiveHaarMeasure E) :
    (generatorValue F (baseExtension F) ψ measures g : ℂ) =
      PadicAbelian.epsilon E.canonicalTopologicalData η (embeddingTraceCharacter F E f ψF)
          μE.measure 0 /
        PadicAbelian.epsilon E.canonicalTopologicalData η' (embeddingTraceCharacter F E f ψF)
          μE.measure 0 := by
  let L := g.extension
  have hval : generatorValue F (baseExtension F) ψ measures g =
      (fieldData F L).abelianEpsilonRatio g.first g.second
        (traceCharacter F (baseExtension F) L g.inclusion ψ)
        (PadicField.AbelianTransport.haarMeasure E (L.asPadicField (p := p)) σ μE) :=
    (fieldData F L).abelianEpsilonRatio_haarIndependent _ _ _ _ _
  have hfac (χ : QuasiCharacter E) :
      (fieldData F L).abelianEpsilonExpression
          (PadicField.ConductorTransport.quasicharacter E (L.asPadicField (p := p)) σ χ)
          (traceCharacter F (baseExtension F) L g.inclusion ψ)
          (PadicField.AbelianTransport.haarMeasure E (L.asPadicField (p := p)) σ μE) =
        PadicAbelian.epsilon E.canonicalTopologicalData χ (embeddingTraceCharacter F E f ψF)
          μE.measure 0 := by
    rw [traceCharacter_eq_additiveCharacter_of_algEquiv F E f L σ hσ g.inclusion ψF ψ hψ]
    refine (PadicField.AbelianTransport.abelianEpsilonExpression_eq E (L.asPadicField (p := p))
      σ χ _ μE).trans ?_
    have h1 : E.canonicalTopologicalData.normalizedAbsPowerCharacter 0 * χ = χ := by
      apply ContinuousMonoidHom.ext
      intro a
      apply Units.ext
      simp
    rw [← PadicAbelian.abelianEpsilonExpression_normalizedAbsPower_mul, h1]
  rw [hval]
  simp only [PadicField.TopologicalData.abelianEpsilonRatio, Units.val_div_eq_div_val]
  rw [hη, hη']
  exact congrArg₂ (· / ·) (hfac η) (hfac η')

end Transport

end Langlands.LocalFactor.NonabelianBrauer
