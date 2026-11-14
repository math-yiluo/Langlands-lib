import Langlands.Representation.RankinSelberg.TwoBlockBaseCasesStatement
import Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement
/-!
# Three two-block analytic base cases for the factors of pairs

The three bases enumerated in JPSS 1983, §7.1, printed pages 438–439,
for both parts of Theorem (3.1), printed pages 404–405. Each target is the
published full multiplicativity statement with two blocks and one additional
arithmetic restriction. The actual ranks are `r + 1`, `t + 1`, `m i + 1`.
The source lower block order reverses in the actual upper induction, so the
adjacent-rank target has `m 0 = 0`. The analytic proofs and the normalized
lower-to-upper equivalence and factor transports are not supplied here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- The dominant-rank base of JPSS §7.1(1), proved in source Section 4:
the test rank `r + 1` is at least the induced rank `t + 1`.
This target asserts certified gamma multiplicativity. -/
def TwoBlockGammaDominantRankStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    t ≤ r →
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) (∏ i, G i)

/-- The dominant-rank base of JPSS §7.1(1), proved in source Section 4:
the test rank `r + 1` is at least the induced rank `t + 1`.
This target asserts certified L-polynomial divisibility. -/
def TwoBlockLDominantRankStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    t ≤ r →
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P

/-- The adjacent-rank base of JPSS §7.1(2), treated in source Section 6.
The rank-one block is first in the actual upper induction. With the rank sum,
`t = r + 1` and `m 0 = 0` imply `m 1 = r`.
This target asserts certified gamma multiplicativity. -/
def TwoBlockGammaAdjacentRankStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    t = r + 1 → m 0 = 0 →
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) (∏ i, G i)

/-- The adjacent-rank base of JPSS §7.1(2), treated in source Section 6.
The rank-one block is first in the actual upper induction. With the rank sum,
`t = r + 1` and `m 0 = 0` imply `m 1 = r`.
This target asserts certified L-polynomial divisibility. -/
def TwoBlockLAdjacentRankStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    t = r + 1 → m 0 = 0 →
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P

/-- The rank-one test base of JPSS §7.1(3), treated in source §5.1–§5.4:
the actual test rank is `r + 1 = 1`.
This target asserts certified gamma multiplicativity. -/
def TwoBlockGammaRankOneStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    r = 0 →
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) (∏ i, G i)

/-- The rank-one test base of JPSS §7.1(3), treated in source §5.1–§5.4:
the actual test rank is `r + 1 = 1`.
This target asserts certified L-polynomial divisibility. -/
def TwoBlockLRankOneStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    r = 0 →
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P

end Langlands.AllField.RankinSelberg
