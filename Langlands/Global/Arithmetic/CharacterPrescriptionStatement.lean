import Langlands.Global.HeckeCharacter

/-!
# Finite-order Hecke-character prescription and isolation

These are proposition definitions on the actual idele-class characters and
adic completions. Their truth is not installed as an instance or assumption.
-/

noncomputable section

universe u

namespace Langlands.Global

/-- The unrestricted Grunwald--Wang bound, including a prescribed finite-order
character of the whole archimedean idele factor. -/
def FiniteOrderCharacterPrescriptionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K)) (n : ℕ), 0 < n →
    ∀ (η : (v : {v // v ∈ S}) → (FiniteCompletion K v.1)ˣ →ₜ* ℂˣ)
      (ηInf : (InfiniteAdeles K)ˣ →ₜ* ℂˣ),
      (∀ v, η v ^ n = 1) → ηInf ^ n = 1 →
      ∃ χ : HeckeCharacter K,
        χ ^ (2 * n) = 1 ∧
        χ.HasPrescribedFiniteComponents S η ∧
        χ.HasPrescribedInfinityComponent ηInf

/-- Nontriviality on the actual integral-unit filtration. At depth zero this
tests all integral units; at positive depth `r` it tests `1 + m^r`. -/
def NontrivialOnPrincipalUnits
    {K : Type u} [Field K] [NumberField K] (v : FinitePlace K)
    (η : (FiniteCompletion K v)ˣ →ₜ* ℂˣ) (r : ℕ) : Prop :=
  ∃ a : (v.adicCompletionIntegers K)ˣ,
    (a : v.adicCompletionIntegers K) - 1 ∈
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ r ∧
    η (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom a) ≠ 1

/-- Finite-order characters of a nonarchimedean completion can be nontrivial
arbitrarily deeply in its principal units. No common order is prescribed. -/
def LocalCharactersArbitrarilyRamifiedStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (v : FinitePlace K) (r : ℕ),
    ∃ η : (FiniteCompletion K v)ˣ →ₜ* ℂˣ,
      (∃ n : ℕ, 0 < n ∧ η ^ n = 1) ∧ NontrivialOnPrincipalUnits v η r

/-- Prescribe a finite set of local characters while making the character
arbitrarily ramified on a disjoint finite set, and trivial at infinity.
The trivial prescription at a selected place gives the isolation used in
Henniart's comparison of functional equations. -/
def RamifiedTwistIsolationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S T : Finset (FinitePlace K)), Disjoint S T →
    ∀ (η : (v : {v // v ∈ S}) → (FiniteCompletion K v.1)ˣ →ₜ* ℂˣ)
      (r : {v // v ∈ T} → ℕ),
      (∀ v, ∃ n : ℕ, 0 < n ∧ η v ^ n = 1) →
      ∃ χ : HeckeCharacter K,
        χ.HasFiniteOrder ∧
        χ.HasPrescribedFiniteComponents S η ∧
        χ.HasPrescribedInfinityComponent 1 ∧
        ∀ v : {v // v ∈ T},
          NontrivialOnPrincipalUnits v.1 (χ.finiteComponent v.1) (r v)

/-- The coherent finite-character input to globalization and twist isolation.
The CM infinity-type and general-position assertions are separate targets. -/
def CharacterPrescriptionStatement : Prop :=
  FiniteOrderCharacterPrescriptionStatement.{u} ∧
  LocalCharactersArbitrarilyRamifiedStatement.{u} ∧
  RamifiedTwistIsolationStatement.{u}

end Langlands.Global
