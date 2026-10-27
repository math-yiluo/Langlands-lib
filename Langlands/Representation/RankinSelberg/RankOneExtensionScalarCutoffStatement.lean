import Langlands.LocalField.Canonical
import Langlands.LocalFactor.Abelian.Padic
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.RankOneExtensionAnalyticData

/-!
# Same-model scalar Fourier cutoff for the early JPSS Lemma (5.5)

JPSS (1983), Lemma (5.5), formula (9) and its proof, printed 426–427: right
smearing by the one-coordinate transvection against a Schwartz–Bruhat weight
whose plus-sign Fourier transform is the cut-off inverse quasicharacter.
The small-neighborhood refinement replacing `a` by `1` inside the original
coefficient is derived, as explained in the paired Markdown. This module only
defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV

/-- For every open neighborhood `O` of `1`, there are a compact open set
`U ⊆ O` of normalized absolute value one containing `1`, an actual
Schwartz–Bruhat pair `κ, Φ` with `Φ = fourierIntegral ψ ν κ` everywhere,
`Φ 0 = 0` and `Φ a = χ(a)⁻¹` on units in `U`, zero on other units, and one
coefficient `f₁` in the same coefficient model as `f₂`. The coefficient `f₁`
is the global right `κ`-smearing of `f₂` along
`rankOneExtensionSmearingUnipotent t k`, it equals `Φ(a) f₂` on every embedded
lower block `B(a)`, `U` is small enough that `f₂(B(a)) = f₂(B(1))` for
`a ∈ U`, and hence `f₁(B(a))` is `χ(a)⁻¹ f₂(B(1))` on `U` and zero otherwise.
This is a closed proposition definition, not a proof. -/
def RankOneExtensionScalarCutoffStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (t k : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ
      (Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) F.Carrier) V),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    IsSmooth π →
    ∀ (ℓ : glFunctionals ψ ((1 + (t + 1)) + k) π)
      (f₂ : (coefficientModel π ℓ).toSubmodule)
      (χ : Quasicharacter F.Carrier)
      (O : Set F.Carrier), IsOpen O → (1 : F.Carrier) ∈ O →
      ∃ (U : Set F.Carrier) (κ Φ : SchwartzBruhat F.Carrier)
        (f₁ : (coefficientModel π ℓ).toSubmodule),
        IsCompact U ∧ IsOpen U ∧ U ⊆ O ∧ (1 : F.Carrier) ∈ U ∧ (0 : F.Carrier) ∉ U ∧
        (∀ y ∈ U, normalizedAbsoluteValue F.canonicalTopologicalData y = 1) ∧
        Φ 0 = 0 ∧
        (∀ a : F.Carrierˣ, (a : F.Carrier) ∈ U →
          Φ (a : F.Carrier) = ((χ a : ℂˣ) : ℂ)⁻¹) ∧
        (∀ a : F.Carrierˣ, (a : F.Carrier) ∉ U → Φ (a : F.Carrier) = 0) ∧
        (∀ b : F.Carrier, Φ b = fourierIntegral ψ ν.val κ b) ∧
        (∀ h : Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) F.Carrier,
          Integrable
            (fun u => κ u * f₂.val.val (h * rankOneExtensionSmearingUnipotent t k u))
            ν.val.measure ∧
          f₁.val.val h =
            ∫ u, κ u * f₂.val.val (h * rankOneExtensionSmearingUnipotent t k u)
              ∂ν.val.measure) ∧
        (∀ (m : Langlands.GeneralLinear (t + 1) F.Carrier)
          (x : Fin (t + 1) → F.Carrier) (a : F.Carrierˣ),
          f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
            Φ (a : F.Carrier) *
              f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a)) ∧
        (∀ (m : Langlands.GeneralLinear (t + 1) F.Carrier)
          (x : Fin (t + 1) → F.Carrier) (a : F.Carrierˣ), (a : F.Carrier) ∈ U →
          f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
            f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x 1)) ∧
        (∀ (m : Langlands.GeneralLinear (t + 1) F.Carrier)
          (x : Fin (t + 1) → F.Carrier) (a : F.Carrierˣ), (a : F.Carrier) ∈ U →
          f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
            ((χ a : ℂˣ) : ℂ)⁻¹ *
              f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x 1)) ∧
        ∀ (m : Langlands.GeneralLinear (t + 1) F.Carrier)
          (x : Fin (t + 1) → F.Carrier) (a : F.Carrierˣ), (a : F.Carrier) ∉ U →
          f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) = 0

end Langlands.RankinSelberg
