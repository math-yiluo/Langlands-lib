import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.LocalFactor.Abelian.Padic
import Langlands.HarmonicAnalysis.CharacterTransport

/-!
# Change of additive character for the epsilon factor of pairs of equal rank

For irreducible admissible representations `π`, `σ` of `GL_n(F)`, `n = r + 1`,
with central characters `ω_π`, `ω_σ`, and `a ∈ Fˣ`, `ψ^a(x) = ψ(ax)`, the
JPSS epsilon factor with measures self-dual for each character satisfies
`ε(s, π × σ, ψ^a) = ω_π(a)^n ω_σ(a)^n |a|^(n²(s - 1/2)) ε(s, π × σ, ψ)`.
No p-adic original source for this equal-rank formula was found. The
statement is derived from the equal-rank functional equation of the Library
(see the Markdown); Jacquet 2009, Remark 2.2, makes the same computation at
an Archimedean place.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

/-- Change of additive character for the epsilon factor of a pair of equal
rank, with self-dual measures: let `π` and `σ` be irreducible admissible
representations of `GL_n(F)`, `n = r + 1`, with central characters `ω_π` and
`ω_σ`. Let `ψ` be an additive character, `a ∈ Fˣ`, `ν` a Haar measure
self-dual for `ψ` and `ν'` one self-dual for `ψ^a(x) = ψ(ax)`. If
`ε(s, π × σ, ψ) = c q^(-ms)`, `e = (c, m)`, then the pair has an epsilon factor
`ε(s, π × σ, ψ^a) = c' q^(-m's)`, `e' = (c', m')`, and
`ε(s, π × σ, ψ^a) = ω_π(a)^n ω_σ(a)^n |a|^(n²(s - 1/2)) ε(s, π × σ, ψ)`
with `|a| = q^(-ord a)`, that is, `m' = m + n² ord(a)` and
`c' = c ω_π(a)^n ω_σ(a)^n |a|^(-n²/2)`. Internal derived statement (no
p-adic original source); compare Jacquet 2009, Remark 2.2 (Archimedean). -/
def EqualRankEpsilonCharacterChangeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (ωπ ωσ : F.Carrierˣ →* ℂˣ),
    Representation.IsIrreducible π →
    (letI := F.canonicalTopologicalData.topology; Langlands.IsAdmissible π) →
    Representation.IsIrreducible σ →
    (letI := F.canonicalTopologicalData.topology; Langlands.IsAdmissible σ) →
    Classification.HasGLCentralCharacter F.Carrier (r + 1) π ωπ →
    Classification.HasGLCentralCharacter F.Carrier (r + 1) σ ωσ →
    ∀ (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
      (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
      (a : F.Carrierˣ)
      (ν' : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData
        (letI := F.canonicalTopologicalData.topology
         letI := F.canonicalTopologicalData.valuativeRel
         letI := F.canonicalTopologicalData.localField
         ψ.scale a))
      (e : ℂˣ × ℤ),
      IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e →
      ∃ e' : ℂˣ × ℤ,
        IsPadicSymmetricEpsilonFactor F
          (letI := F.canonicalTopologicalData.topology
           letI := F.canonicalTopologicalData.valuativeRel
           letI := F.canonicalTopologicalData.localField
           ψ.scale a) ν'.val π σ e' ∧
        e'.2 = e.2 + ((r + 1) * (r + 1) : ℕ) * F.canonicalTopologicalData.ord (a : F.Carrier) ∧
        (e'.1 : ℂ) = (e.1 : ℂ) * ((ωπ a : ℂˣ) : ℂ) ^ (r + 1) * ((ωσ a : ℂˣ) : ℂ) ^ (r + 1) *
          ((F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^
            (-(((r + 1) * (r + 1) : ℕ) : ℂ) / 2)

end Langlands.RankinSelberg
