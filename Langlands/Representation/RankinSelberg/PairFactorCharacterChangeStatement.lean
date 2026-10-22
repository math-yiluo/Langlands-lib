import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.LocalFactor.Abelian.Padic
import Langlands.HarmonicAnalysis.CharacterTransport

/-!
# Change of additive character for factors of pairs of unequal rank

Cogdell and Piatetski-Shapiro 1994, Lemma 2.1 and its proof (printed pages
161–163): for representations `Π` of `GL_n(F)` and `τ` of `GL_m(F)`, `m < n`,
with central characters `ω_Π`, `ω_τ`, and `λ ∈ Fˣ`, `ψ^λ(x) = ψ(λx)`, the
L-factor `L(s, Π × τ)` does not depend on `ψ`, and
`ε(s, Π × τ, ψ^λ) = ω_Π(λ)^m ω_τ(λ)^n |λ|^(nms - d) ε(s, Π × τ, ψ)`.
The printed `d = nm - m(m+1)/2` belongs to one fixed Haar measure for both
characters; for the JPSS relation `IsPadicSymmetricEpsilonFactor`, with the
measure self-dual for each character, the same computation gives `d = nm/2`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

/-- Cogdell and Piatetski-Shapiro 1994, printed page 162 ("the local
L-functions are independent of the choice of `ψ_v`"), for pairs of unequal rank:
let `π` and `σ` be irreducible admissible representations of `GL_(r+1)(F)` and
`GL_(t+1)(F)`, `r ≠ t`. For every additive character `ψ`, every Haar measure `ν`
and every `a ∈ Fˣ`, an L-polynomial of the pair for `ψ` is one for
`ψ^a(x) = ψ(ax)`. -/
def UnequalRankLPolynomialCharacterChangeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    r ≠ t →
    Representation.IsIrreducible π →
    (letI := F.canonicalTopologicalData.topology; Langlands.IsAdmissible π) →
    Representation.IsIrreducible σ →
    (letI := F.canonicalTopologicalData.topology; Langlands.IsAdmissible σ) →
    ∀ (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
      (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
        AdditiveHaarMeasure F.Carrier)
      (a : F.Carrierˣ) (P : ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν π σ P →
      IsPadicSymmetricLPolynomial F
        (letI := F.canonicalTopologicalData.topology
         letI := F.canonicalTopologicalData.valuativeRel
         letI := F.canonicalTopologicalData.localField
         ψ.scale a) ν π σ P

/-- Cogdell and Piatetski-Shapiro 1994, proof of Lemma 2.1 (printed pages
161–163), with self-dual measures: let `π` and `σ` be irreducible admissible
representations of `GL_(r+1)(F)` and `GL_(t+1)(F)`, `r ≠ t`, with central
characters `ω_π` and `ω_σ`. Let `ψ` be an additive character, `a ∈ Fˣ`, `ν` a
Haar measure self-dual for `ψ` and `ν'` one self-dual for `ψ^a(x) = ψ(ax)`. If
`ε(s, π × σ, ψ) = c q^(-ms)`, `e = (c, m)`, then the pair has an epsilon factor
`ε(s, π × σ, ψ^a) = c' q^(-m's)`, `e' = (c', m')`, and
`ε(s, π × σ, ψ^a) = ω_π(a)^(t+1) ω_σ(a)^(r+1) |a|^(N(s - 1/2)) ε(s, π × σ, ψ)`
with `N = (r+1)(t+1)` and `|a| = q^(-ord a)`, that is,
`m' = m + N ord(a)` and `c' = c ω_π(a)^(t+1) ω_σ(a)^(r+1) |a|^(-N/2)`. -/
def UnequalRankEpsilonCharacterChangeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (ωπ ωσ : F.Carrierˣ →* ℂˣ),
    r ≠ t →
    Representation.IsIrreducible π →
    (letI := F.canonicalTopologicalData.topology; Langlands.IsAdmissible π) →
    Representation.IsIrreducible σ →
    (letI := F.canonicalTopologicalData.topology; Langlands.IsAdmissible σ) →
    Classification.HasGLCentralCharacter F.Carrier (r + 1) π ωπ →
    Classification.HasGLCentralCharacter F.Carrier (t + 1) σ ωσ →
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
        e'.2 = e.2 + ((r + 1) * (t + 1) : ℕ) * F.canonicalTopologicalData.ord (a : F.Carrier) ∧
        (e'.1 : ℂ) = (e.1 : ℂ) * ((ωπ a : ℂˣ) : ℂ) ^ (t + 1) * ((ωσ a : ℂˣ) : ℂ) ^ (r + 1) *
          ((F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^
            (-(((r + 1) * (t + 1) : ℕ) : ℂ) / 2)

/-- The change of additive character for factors of pairs of unequal rank
(Cogdell–Piatetski-Shapiro 1994, Lemma 2.1 and its proof): the L-polynomial
does not change and the epsilon factor changes by
`ω_π(a)^(t+1) ω_σ(a)^(r+1) |a|^((r+1)(t+1)(s - 1/2))`. -/
def PairFactorCharacterChangeStatement : Prop :=
  UnequalRankLPolynomialCharacterChangeStatement.{uF, uV, uW} ∧
    UnequalRankEpsilonCharacterChangeStatement.{uF, uV, uW}

end Langlands.RankinSelberg
