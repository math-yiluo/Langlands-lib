import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Induction.BlockFactors

/-!
# Multiplicativity of the factors of pairs

JPSS 1983, Theorem (3.1), printed pages 404-405: for `π` of Whittaker type on
`GL_r(F)` and `σ = Ind(σ_1, …, σ_p)` induced from representations of Whittaker
type on the blocks of a standard parabolic of `GL_t(F)`, the gamma factor of
`π × σ` is the product of the gamma factors of `π × σ_i`, and
`L(s, π × σ)` lies in `∏ L(s, π × σ_i) ℂ[q^(-s), q^s]`. The factors are the
relations `IsPadicSymmetricGammaFactor` and `IsPadicSymmetricLPolynomial` with
the self-dual measure, which cover both rank orders. The induced
representation is the published normalized induction
`canonicalNormalizedProductInduced` from the standard upper block parabolic.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

/-- The block shape of rank `t + 1` with the `k` block sizes `m i + 1`. -/
abbrev succBlockShape {k t : ℕ} (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1) :
    BlockShape (t + 1) where
  length := k
  size i := m i + 1
  positive i := Nat.succ_pos (m i)
  sum_eq := h

/-- JPSS 1983, Theorem (3.1)(i) (printed page 405). Let `π` be a representation
of Whittaker type of `GL_(r+1)(F)`, and `σ_1, …, σ_k` representations of
Whittaker type of `GL_(m_i + 1)(F)` with `∑ (m_i + 1) = t + 1`. Then each pair
`(π, σ_i)` has a gamma factor `G_i`, and their product is the gamma factor of
`π` against the normalized induction of `(σ_1, …, σ_k)` to `GL_(t+1)(F)`. -/
def GammaMultiplicativityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t k : ℕ) (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ G : Fin k → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) (∏ i, G i)

/-- JPSS 1983, Theorem (3.1)(ii) (printed page 405), with the hypotheses of
`GammaMultiplicativityStatement`: the L-polynomials `P` of `π` against the
induced representation and `P_i` of `(π, σ_i)` exist, and
`L(s, π × σ) ∈ ∏ L(s, π × σ_i) ℂ[q^(-s), q^s]`, that is,
`X^e ∏ P_i = Q P` for a polynomial `Q` and some `e`. -/
def LFactorMultiplicativityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t k : ℕ) (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ (P : ℂ[X]) (Pi : Fin k → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P

/-- Both parts of JPSS 1983, Theorem (3.1). -/
def MultiplicativityStatement : Prop :=
  GammaMultiplicativityStatement.{uF, uV, uW} ∧ LFactorMultiplicativityStatement.{uF, uV, uW}

end Langlands.RankinSelberg
