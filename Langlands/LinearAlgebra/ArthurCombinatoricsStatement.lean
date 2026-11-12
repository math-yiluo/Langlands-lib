import Langlands.LinearAlgebra.ArthurCombinatorics

/-! # Statements of Arthur's combinatorial lemmas

Arthur 1978, Proposition 1.1, Lemma 6.1, the identity after Corollary 6.2 and Lemma 6.3
(Langlands' combinatorial lemma); Arthur 2005, (8.2) and Lemma 8.3. The objects are those of
`Langlands.LinearAlgebra.ArthurCombinatorics`, for a crystallographic root system over `ℝ` with a
base `b`; standard parabolic subgroups are subsets of `b.support`. -/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.ArthurCombinatorics

/-- Arthur 1978, Proposition 1.1 (Arthur 2005, Identity 6.2): for `Θ₁ ⊆ Θ₂`,
`∑_{Θ₁ ⊆ Θ ⊆ Θ₂} (−1)^{|Θ₂ \ Θ|}` is `1` if `Θ₁ = Θ₂` and `0` otherwise. -/
def AlternatingSumStatement : Prop :=
  ∀ {ι : Type u} [DecidableEq ι] (Θ₁ Θ₂ : Finset ι), Θ₁ ⊆ Θ₂ →
    ∑ Θ ∈ Θ₂.powerset.filter (Θ₁ ⊆ ·), (-1 : ℤ) ^ (Θ₂ \ Θ).card = if Θ₁ = Θ₂ then 1 else 0

/-- The identity after Arthur 1978, Corollary 6.2, in the relative form used in the proof of
Lemma 6.3: for standard parabolic subgroups `R ⊊ P`,
`∑_{R ⊆ P_1 ⊆ P} (−1)^{dim(A_1/A_P)} τ_R^{P_1}(H) τ̂_{P_1}^P(H) = 0` for every `H`. -/
def TauTauHatVanishingStatement : Prop :=
  ∀ {ι M N : Type u} [DecidableEq ι] [Finite ι] [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] (b : P.Base) (ΘR ΘP : Finset ι),
    ΘR ⊆ ΘP → ΘP ⊆ b.support → ΘR ≠ ΘP → ∀ H : N,
      ∑ Θ₁ ∈ ΘP.powerset.filter (ΘR ⊆ ·),
        (-1 : ℤ) ^ (ΘP \ Θ₁).card * tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H = 0

/-- Arthur 1978, Lemma 6.1: for `P_1 ⊆ P_2`, `σ_{P_1}^{P_2}(H)` is `1` exactly when
(i) `α(H) > 0` for `α ∈ Δ_1^2`, (ii) `α(H) ≤ 0` for `α ∈ Δ_1 \ Δ_1^2`, and (iii) `ϖ(H) > 0` for
`ϖ ∈ Δ̂_2`, the roots being evaluated at `H_{P_1}`; otherwise it is `0`. -/
def SigmaCharacterizationStatement : Prop :=
  ∀ {ι M N : Type u} [DecidableEq ι] [Finite ι] [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] (b : P.Base) (Θ₁ Θ₂ : Finset ι),
    Θ₁ ⊆ Θ₂ → Θ₂ ⊆ b.support → ∀ H : N,
      sigma P b.support Θ₁ Θ₂ H =
        if (∀ i ∈ Θ₂ \ Θ₁, 0 < P.root' i (levelProjection P Θ₁ H)) ∧
            (∀ i ∈ b.support \ Θ₂, P.root' i (levelProjection P Θ₁ H) ≤ 0) ∧
            (∀ i ∈ b.support \ Θ₂, 0 < weightCoordinate P b.support i H) then 1 else 0

/-- Arthur 1978, Lemma 6.3 (Langlands' combinatorial lemma): for `Q ⊆ P` and `Λ ∈ 𝔞_0^*`,
`∑_{Q ⊆ R ⊆ P} ε_Q^R(Λ) φ_Q^R(Λ, H) τ_R^P(H)` is `0` if `Λ(α^∨) ≤ 0` for some `α ∈ Δ_Q^P`, and `1`
otherwise. -/
def LanglandsCombinatorialLemmaStatement : Prop :=
  ∀ {ι M N : Type u} [DecidableEq ι] [Finite ι] [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] (b : P.Base) (ΘQ ΘP : Finset ι),
    ΘQ ⊆ ΘP → ΘP ⊆ b.support → ∀ (Λ : M) (H : N),
      ∑ ΘR ∈ ΘP.powerset.filter (ΘQ ⊆ ·),
          epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H * tau P ΘR ΘP H =
        if ∃ i ∈ ΘP \ ΘQ, corootValue P ΘQ Λ i ≤ 0 then 0 else 1

/-- Arthur 2005, (8.2): for `P_1 ⊆ P`, `τ_{P_1}^P(H) τ̂_P(H) = ∑_{P_2 ⊇ P} σ_{P_1}^{P_2}(H)`. -/
def TauTauHatSigmaExpansionStatement : Prop :=
  ∀ {ι M N : Type u} [DecidableEq ι] [Finite ι] [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] (b : P.Base) (Θ₁ ΘP : Finset ι),
    Θ₁ ⊆ ΘP → ΘP ⊆ b.support → ∀ H : N,
      tau P Θ₁ ΘP H * tauHat P ΘP b.support H =
        ∑ Θ₂ ∈ b.support.powerset.filter (ΘP ⊆ ·), sigma P b.support Θ₁ Θ₂ H

/-- Arthur 2005, Lemma 8.3: for `P_1 ⊆ P_2`, (a) `σ_{P_1}^{P_2}` takes only the values `0` and
`1`; (b) there is `c` such that if `H_1 = H_1^2 + H_2` with `H_1^2 ∈ 𝔞_{P_1}^{P_2}`,
`H_2 ∈ 𝔞_{P_2}^G` and `σ_{P_1}^{P_2}(H_1) = 1`, then `τ_{P_1}^{P_2}(H_1^2) = 1` and
`‖H_2‖ ≤ c ‖H_1^2‖`, for the `ℓ¹` norm in the coroot basis of `b`. -/
def SigmaSupportStatement : Prop :=
  ∀ {ι M N : Type u} [DecidableEq ι] [Finite ι] [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] (b : P.Base) (Θ₁ Θ₂ : Finset ι),
    Θ₁ ⊆ Θ₂ → Θ₂ ⊆ b.support →
      (∀ H : N, sigma P b.support Θ₁ Θ₂ H = 0 ∨ sigma P b.support Θ₁ Θ₂ H = 1) ∧
      ∃ c : ℝ, ∀ H₁₂ H₂ : N, H₁₂ ∈ rootAnnihilator P Θ₁ ⊓ corootSpan P Θ₂ →
        H₂ ∈ rootAnnihilator P Θ₂ → sigma P b.support Θ₁ Θ₂ (H₁₂ + H₂) = 1 →
          tau P Θ₁ Θ₂ H₁₂ = 1 ∧
            ∑ i, |b.toCoweightBasis.repr H₂ i| ≤ c * ∑ i, |b.toCoweightBasis.repr H₁₂ i|

/-- Arthur's combinatorial lemmas: the conjunction of the statements of this module. -/
def ArthurCombinatoricsStatement : Prop :=
  AlternatingSumStatement.{u} ∧ TauTauHatVanishingStatement.{u} ∧
    SigmaCharacterizationStatement.{u} ∧ LanglandsCombinatorialLemmaStatement.{u} ∧
    TauTauHatSigmaExpansionStatement.{u} ∧ SigmaSupportStatement.{u}

end Langlands.ArthurCombinatorics
