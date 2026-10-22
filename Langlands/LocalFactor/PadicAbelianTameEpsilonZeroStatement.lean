import Langlands.LocalFactor.PadicAbelianEpsilonZeroStatement

/-!
# Deligne's tame Gauss-sum formula for `ε₀`

Deligne (5.10): for a quasicharacter `χ` of conductor at most one, an additive
character `ψ` of conductor `-1` and a Haar measure giving the maximal ideal volume
one, `ε₀(χ, ψ, dx)` is minus the Gauss sum of the residue characters of `χ` and
`ψ`. The residue characters are read through an arbitrary section of the actual
residue map on residue units. The statement below is a proposition only.
-/

noncomputable section

namespace Langlands.LocalFactor.PadicAbelian

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

/-- Deligne's Gauss sum (5.10.2), `τ(χ_k, ψ_k) = -∑_{x ∈ k^×} χ_k⁻¹(x) ψ_k(x)`,
with `χ_k(x) = χ(σ x)` and `ψ_k(x) = ψ(σ x)` for a supplied map `σ` from the
residue units to the integers. It is the residue Gauss sum when `σ` is a section
of the residue map, `χ` has conductor at most one and `ψ` is trivial on the
maximal ideal. -/
def residueGaussSum (χ : MultiplicativeCharacter) (ψ : AddChar F.Carrier Circle)
    (σ : T.ResidueFieldˣ → T.Integers) : ℂ :=
  -∑ᶠ x : T.ResidueFieldˣ,
    (characterExtension T χ ((σ x : T.Integers) : F.Carrier))⁻¹ *
      (ψ ((σ x : T.Integers) : F.Carrier) : ℂ)

end Langlands.LocalFactor.PadicAbelian

namespace Langlands.LocalFactor

universe u

/-- Deligne (5.10.1), (5.10.2) and (5.10.3), at every uniformizer `π`, every
quasicharacter `χ` of conductor `a ≤ 1`, every additive character `ψ` of conductor
`-1` and every section `σ` of the residue map on residue units. Clause 1 is
`ε₀(χ ω_s, ψ, dx) = -τ(χ_k, ψ_k)` when the ideal `(π)` has volume one; clause 2
is `τ(1, ψ_k) = 1`; clause 3 is `ε₀([χ ω_s] - [ω_s], ψ, dx) = τ(χ_k, ψ_k)` for
every Haar measure. This is a theorem target, not a theorem proof. -/
def PadicAbelianTameEpsilonZeroStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  ∀ (π : F.Carrierˣ), T.ord (π : F.Carrier) = 1 →
  ∀ (χ : HarmonicAnalysis.Quasicharacter F.Carrier) (a : ℕ),
    PadicAbelian.ConductorAt T χ a → a ≤ 1 →
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier),
    PadicAbelian.AdditiveConductorAt T ψ.toAddChar (-1) →
  ∀ (σ : T.ResidueFieldˣ → T.Integers),
    (∀ x : T.ResidueFieldˣ, T.residue (σ x) = (x : T.ResidueField)) →
  (∀ μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier,
    μ.measure ((fun v => (π : F.Carrier) * v) '' PadicAbelian.integerRing T) = 1 →
    ∀ s : ℂ,
      PadicAbelian.epsilonZeroAt T π χ ψ.toAddChar μ.measure a (-1) s =
        -PadicAbelian.residueGaussSum T χ ψ.toAddChar σ) ∧
  (a = 0 → PadicAbelian.residueGaussSum T χ ψ.toAddChar σ = 1) ∧
  (∀ (μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier) (s : ℂ),
    PadicAbelian.epsilonZeroAt T π χ ψ.toAddChar μ.measure a (-1) s *
        (PadicAbelian.epsilonZeroAt T π 1 ψ.toAddChar μ.measure 0 (-1) s)⁻¹ =
      PadicAbelian.residueGaussSum T χ ψ.toAddChar σ)

end Langlands.LocalFactor
