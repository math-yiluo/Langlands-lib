import Langlands.LocalFactor.Abelian.Padic

/-!
# Deligne's modified constant `ε₀` in rank one

Deligne (3.4.3.3) defines `ε₀` of a quasicharacter `χ` of a p-adic field by
`ε = ε₀` for `χ` ramified and `ε = ε₀ · (-χ(π))⁻¹` for `χ` unramified. Here it is
evaluated at `χ ω_s` from the published rank-one expression `epsilonAt`. The
statement below is Deligne's (3.4.3.4) and (3.4.3.5) for `ε₀`, together with its
spectral form and its independence of the uniformizer. It is a proposition only.
-/

noncomputable section

open MeasureTheory

namespace Langlands.LocalFactor.PadicAbelian

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- Deligne (3.4.3.3) at `χ ω_s`, at specified conductor levels `a` of `χ` and `n`
of `ψ`: `ε₀ = -(χ ω_s)(π) · ε` if `a = 0`, and `ε₀ = ε` otherwise. Here
`(χ ω_s)(π) = χ(π) q^(-s)`. -/
def epsilonZeroAt (π : F.Carrierˣ) (χ : MultiplicativeCharacter)
    (ψ : AddChar F.Carrier Circle) (μ : BorelMeasure T)
    (a : ℕ) (n : ℤ) (s : ℂ) : ℂ :=
  if a = 0 then -((χ π : ℂ) * spectralVariable T s) * epsilonAt T π χ ψ μ a n s
  else epsilonAt T π χ ψ μ a n s

/-- `ε₀(χ ω_s, ψ, μ)` at the actual conductors and the owner's uniformizer. -/
def epsilonZero (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : BorelMeasure T) (s : ℂ) : ℂ :=
  letI := T.topology
  epsilonZeroAt T (uniformizerUnit T) χ ψ.toAddChar μ
    (T.multiplicativeConductor χ) (T.additiveConductor ψ) s

end Langlands.LocalFactor.PadicAbelian

namespace Langlands.LocalFactor

universe u

/-- Deligne (3.4.3.4) and (3.4.3.5) for `ε₀`, at every uniformizer, every
quasicharacter `χ` of conductor `a`, every Haar measure and every additive
character of conductor `n`, with `sw(χ) + 1 = (a - 1 : ℕ) + 1` in truncated
subtraction. This is a theorem target, not a theorem proof. -/
def PadicAbelianEpsilonZeroStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  ∀ (π : F.Carrierˣ), T.ord (π : F.Carrier) = 1 →
  ∀ (χ : HarmonicAnalysis.Quasicharacter F.Carrier) (a : ℕ), PadicAbelian.ConductorAt T χ a →
  ∀ (μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier) (n : ℤ),
    PadicAbelian.AdditiveConductorAt T ψ.toAddChar n →
  (∀ c : F.Carrierˣ, T.ord (c : F.Carrier) = n + ((a - 1 : ℕ) : ℤ) + 1 → ∀ s : ℂ,
    PadicAbelian.epsilonZeroAt T π χ ψ.toAddChar μ.measure a n s =
      ∫ x in (fun v => (c⁻¹ : F.Carrierˣ) * v) '' PadicAbelian.integralUnits T,
        PadicAbelian.gaussIntegrand T χ ψ.toAddChar s x ∂μ.measure) ∧
  (∀ ω : HarmonicAnalysis.Quasicharacter F.Carrier, PadicAbelian.ConductorAt T ω 0 →
    ∀ s : ℂ,
      PadicAbelian.epsilonZeroAt T π (χ * ω) ψ.toAddChar μ.measure a n s =
        (ω π : ℂ) ^ (n + ((a - 1 : ℕ) : ℤ) + 1) *
          PadicAbelian.epsilonZeroAt T π χ ψ.toAddChar μ.measure a n s) ∧
  (∀ s : ℂ,
    PadicAbelian.epsilonZeroAt T π χ ψ.toAddChar μ.measure a n s =
      PadicAbelian.epsilonZeroAt T π χ ψ.toAddChar μ.measure a n 0 *
        Complex.exp (-((n + ((a - 1 : ℕ) : ℤ) + 1 : ℤ) : ℂ) * s *
          (Real.log (T.residueCardinality : ℝ) : ℂ))) ∧
  (∀ (ρ : F.Carrierˣ), T.ord (ρ : F.Carrier) = 1 → ∀ s : ℂ,
    PadicAbelian.epsilonZeroAt T ρ χ ψ.toAddChar μ.measure a n s =
      PadicAbelian.epsilonZeroAt T π χ ψ.toAddChar μ.measure a n s)

end Langlands.LocalFactor
