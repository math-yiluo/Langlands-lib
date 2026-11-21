import Langlands.BaseChange.OrbitalIntegral

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.QuotientIntegration
  Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v w

private theorem twistedOrbitalIntegral_mul_of_orbitValue {G : Type w} [Group G]
    [TopologicalSpace G] (ε : G →* G) (g : G)
    (ν : Measure (LeftQuotient (twistedCentralizer ε g)))
    (f weight : G → ℂ) (a : ℂ) (h : ∀ x : G, weight (x⁻¹ * g * ε x) = a) :
    twistedOrbitalIntegral ε g ν (fun x => f x * weight x) =
      twistedOrbitalIntegral ε g ν f * a := by
  unfold twistedOrbitalIntegral
  rw [← integral_mul_const]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h x => simp only [twistedOrbitFunction_mk, h]

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  {n : ℕ} {σ : E ≃ₐ[F] E} {l : ℕ}
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  {μF : Measure (GeneralLinear n F)} {μE : Measure (GeneralLinear n E)}
  {φ : GeneralLinear n E → ℂ} {f : GeneralLinear n F → ℂ}

/-- Concordance is preserved by multiplication by weights with the same value on associated
orbits and with the ordinary weight constant along every regular conjugacy class. -/
theorem AreConcordant.mul_of_orbitValues (h : AreConcordant σ l μF μE φ f)
    (Θ : GeneralLinear n E → ℂ) (θ : GeneralLinear n F → ℂ)
    (hF : ∀ γ : GeneralLinear n F, IsRegularSemisimple γ →
      ∀ x : GeneralLinear n F, θ (x⁻¹ * γ * x) = θ γ)
    (hE : ∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F),
      IsNormAssociated σ l δ γ → IsRegularSemisimple γ →
      ∀ x : GeneralLinear n E, Θ (x⁻¹ * δ * entrywiseAut σ n x) = θ γ) :
    AreConcordant σ l μF μE (fun δ => φ δ * Θ δ) (fun γ => f γ * θ γ) := by
  have hord (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ)
      (νγ : Measure (LeftQuotient (glCentralizer γ))) :
      orbitalIntegral γ νγ (fun y => f y * θ y) = orbitalIntegral γ νγ f * θ γ :=
    twistedOrbitalIntegral_mul_of_orbitValue (MonoidHom.id _) γ νγ f θ (θ γ) (hF γ hγ)
  constructor
  · intro γ hγ hnorm μγ _ _ νγ hνγ
    rw [hord γ hγ νγ, h.1 γ hγ hnorm μγ νγ hνγ, zero_mul]
  · intro δ γ hassoc hγ μδ _ _ μγ _ _ νδ νγ hνδ hνγ hμ
    have htw : sigmaOrbitalIntegral σ n δ νδ (fun x => φ x * Θ x) =
        sigmaOrbitalIntegral σ n δ νδ φ * θ γ :=
      twistedOrbitalIntegral_mul_of_orbitValue (entrywiseAut σ n).toMonoidHom
        δ νδ φ Θ (θ γ) (hE δ γ hassoc hγ)
    rw [htw, hord γ hγ νγ, h.2 δ γ hassoc hγ μδ μγ νδ νγ hνδ hνγ hμ]

end Langlands.BaseChange
