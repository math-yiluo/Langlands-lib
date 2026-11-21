import Langlands.TraceFormula.TwistedOrbital
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Twisted orbital integrals of product functions on product groups

These statements give the twisted orbital integral of a product of continuous
test functions on two groups or on a finite family of groups. They assume
componentwise twists, compatible quotient measures, a product normalization of
the centralizer measure, and integrability of each factor's orbit function.
They assert integrability of the product orbit function and factorization
of its integral.

The statements generalize the finite splitting step in Getz–Hahn (2024),
Lemma 17.8.3 and equation (17.55) (printed pp. 463–464), using the twisted
orbital integral in (18.32) (printed p. 487).
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.QuotientIntegration

universe u w

/-- Product formula for twisted orbital integrals on a product of two groups. Let `θ` be a
twist of `G₁ × G₂` acting componentwise by continuous endomorphisms `θ₁`, `θ₂`. Suppose that
the measure `μC` on the `θ`-centralizer of `(δ₁, δ₂)`, pushed to `G₁ × G₂`, is the product
of the pushforwards of the measures `μC₁`, `μC₂` on the `θᵢ`-centralizers of `δᵢ`, and that the
quotient measures `ν₁`, `ν₂`, `ν` are compatible with these and with `μ₁`, `μ₂`, `μ₁ × μ₂`.
Then for continuous `f₁`, `f₂` with integrable twisted orbit functions, the twisted orbit
function of `(x₁, x₂) ↦ f₁ x₁ * f₂ x₂` is integrable and its twisted orbital integral at
`(δ₁, δ₂)` is the product of the twisted orbital integrals of `f₁` at `δ₁` and of `f₂` at
`δ₂`. -/
def ProdTwistedOrbitalIntegralStatement : Prop :=
  ∀ {G₁ G₂ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [T2Space G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    [T2Space G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂]
    [MeasurableSpace G₂] [BorelSpace G₂]
    (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
    (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (θ : G₁ × G₂ →* G₁ × G₂),
    Continuous θ₁ → Continuous θ₂ → (∀ x, θ x = (θ₁ x.1, θ₂ x.2)) →
    ∀ (δ₁ : G₁) (δ₂ : G₂)
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ₁ δ₁))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ₁ δ₁))]
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ₂ δ₂))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ₂ δ₂))]
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ (δ₁, δ₂)))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ (δ₁, δ₂)))]
    (μC₁ : Measure (twistedCentralizer θ₁ δ₁))
    [μC₁.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC₁] [μC₁.IsOpenPosMeasure]
    (μC₂ : Measure (twistedCentralizer θ₂ δ₂))
    [μC₂.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC₂] [μC₂.IsOpenPosMeasure]
    (μC : Measure (twistedCentralizer θ (δ₁, δ₂)))
    [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    (ν₁ : Measure (LeftQuotient (twistedCentralizer θ₁ δ₁)))
    (ν₂ : Measure (LeftQuotient (twistedCentralizer θ₂ δ₂)))
    (ν : Measure (LeftQuotient (twistedCentralizer θ (δ₁, δ₂)))),
    IsCompatible (twistedCentralizer θ₁ δ₁) μ₁ μC₁ ν₁ →
    IsCompatible (twistedCentralizer θ₂ δ₂) μ₂ μC₂ ν₂ →
    IsCompatible (twistedCentralizer θ (δ₁, δ₂)) (μ₁.prod μ₂) μC ν →
    μC.map Subtype.val = (μC₁.map Subtype.val).prod (μC₂.map Subtype.val) →
    ∀ (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ), Continuous f₁ → Continuous f₂ →
      Integrable (twistedOrbitFunction θ₁ δ₁ f₁) ν₁ →
      Integrable (twistedOrbitFunction θ₂ δ₂ f₂) ν₂ →
      Integrable (twistedOrbitFunction θ (δ₁, δ₂) fun x => f₁ x.1 * f₂ x.2) ν ∧
        twistedOrbitalIntegral θ (δ₁, δ₂) ν (fun x => f₁ x.1 * f₂ x.2) =
          twistedOrbitalIntegral θ₁ δ₁ ν₁ f₁ * twistedOrbitalIntegral θ₂ δ₂ ν₂ f₂

/-- Product formula for twisted orbital integrals on a finite product of groups. Let `θ` be a
twist of `Π i, G i` acting componentwise by continuous endomorphisms `θ' i`. Suppose that
the measure `μC` on the `θ`-centralizer of `δ`, pushed to `Π i, G i`, is the product of the
pushforwards of the measures `μC' i` on the `θ' i`-centralizers of `δ i`, and that the quotient
measures `ν' i`, `ν` are compatible with these and with `μ i`, `Measure.pi μ`. Then for
continuous `f i` with integrable twisted orbit functions, the twisted orbit function of
`x ↦ ∏ i, f i (x i)` is integrable and its twisted orbital integral at `δ` is the product over
`i` of the twisted orbital integrals of `f i` at `δ i`. -/
def PiTwistedOrbitalIntegralStatement : Prop :=
  ∀ {ι : Type w} [Fintype ι] {G : ι → Type u} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (θ' : ∀ i, G i →* G i) (θ : (∀ i, G i) →* ∀ i, G i),
    (∀ i, Continuous (θ' i)) → (∀ x i, θ x i = θ' i (x i)) →
    ∀ (δ : ∀ i, G i)
    [∀ i, MeasurableSpace (LeftQuotient (twistedCentralizer (θ' i) (δ i)))]
    [∀ i, BorelSpace (LeftQuotient (twistedCentralizer (θ' i) (δ i)))]
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]
    (μC' : ∀ i, Measure (twistedCentralizer (θ' i) (δ i)))
    [∀ i, (μC' i).IsMulRightInvariant] [∀ i, IsFiniteMeasureOnCompacts (μC' i)]
    [∀ i, (μC' i).IsOpenPosMeasure]
    (μC : Measure (twistedCentralizer θ δ))
    [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    (ν' : ∀ i, Measure (LeftQuotient (twistedCentralizer (θ' i) (δ i))))
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))),
    (∀ i, IsCompatible (twistedCentralizer (θ' i) (δ i)) (μ i) (μC' i) (ν' i)) →
    IsCompatible (twistedCentralizer θ δ) (Measure.pi μ) μC ν →
    μC.map Subtype.val = Measure.pi (fun i => (μC' i).map Subtype.val) →
    ∀ f : ∀ i, G i → ℂ, (∀ i, Continuous (f i)) →
      (∀ i, Integrable (twistedOrbitFunction (θ' i) (δ i) (f i)) (ν' i)) →
      Integrable (twistedOrbitFunction θ δ fun x => ∏ i, f i (x i)) ν ∧
        twistedOrbitalIntegral θ δ ν (fun x => ∏ i, f i (x i)) =
          ∏ i, twistedOrbitalIntegral (θ' i) (δ i) (ν' i) (f i)

end Langlands.TraceFormula
