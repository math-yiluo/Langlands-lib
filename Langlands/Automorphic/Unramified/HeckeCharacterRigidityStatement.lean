import Langlands.Global.HeckeCharacter
import Mathlib.Algebra.Polynomial.Basic

/-!
# Unramified rigidity for actual Hecke characters

These are proposition targets, not proofs. They express the rank-one
Jacquet--Shalika input using the published characters of the actual idele-class
group. Higher-rank automorphic statements remain separate.
-/

universe u

namespace Langlands.Automorphic.Unramified

open Langlands.Global

/-- A continuous Hecke quasi-character is unramified outside finitely many
finite places. -/
def HeckeFiniteRamificationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (χ : HeckeCharacter K),
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S, χ.IsUnramifiedAt v

/-- Rank-one power-trace independence, with actual local uniformizers and all
strictly positive powers. Characters need not be unitary or of finite order. -/
def HeckePowerTraceIndependenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (r : ℕ) (χ : Fin r → HeckeCharacter K),
    Function.Injective χ →
    ∀ (S : Finset (FinitePlace K)),
      (∀ i v, v ∉ S → (χ i).IsUnramifiedAt v) →
      ∀ (c : Fin r → ℂ),
        (∀ (v : FinitePlace K), v ∉ S →
          ∀ (π : (FiniteCompletion K v)ˣ),
            Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
            ∀ k : ℕ, 0 < k →
              ∑ i : Fin r, c i * ((χ i).finiteComponent v π : ℂ) ^ k = 0) →
        ∀ i, c i = 0

/-- Equality of unramified products of rank-one Euler polynomials determines
finite Hecke-character families, including their multiplicities. -/
def HeckeEulerProductRigidityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (r s : ℕ) (χ : Fin r → HeckeCharacter K) (η : Fin s → HeckeCharacter K)
    (S : Finset (FinitePlace K)),
    (∀ i v, v ∉ S → (χ i).IsUnramifiedAt v) →
    (∀ j v, v ∉ S → (η j).IsUnramifiedAt v) →
    (∀ (v : FinitePlace K), v ∉ S →
      ∀ (π : (FiniteCompletion K v)ˣ),
        Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
        (∏ i : Fin r, (1 - Polynomial.C ((χ i).finiteComponent v π : ℂ) *
          Polynomial.X)) =
        ∏ j : Fin s, (1 - Polynomial.C ((η j).finiteComponent v π : ℂ) *
          Polynomial.X)) →
    ∃ e : Fin r ≃ Fin s, ∀ i, χ i = η (e i)

/-- Almost-everywhere equality of unramified local components determines a
Hecke character on the entire idele-class group. -/
def HeckeLocalComponentRigidityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (χ η : HeckeCharacter K) (S : Finset (FinitePlace K)),
    (∀ v ∉ S, χ.IsUnramifiedAt v ∧ η.IsUnramifiedAt v ∧
      χ.finiteComponent v = η.finiteComponent v) →
    χ = η

/-- Coherent rank-one finite-ramification and unramified-rigidity targets. -/
def HeckeCharacterRigidityStatement : Prop :=
  HeckeFiniteRamificationStatement.{u} ∧
  HeckePowerTraceIndependenceStatement.{u} ∧
  HeckeEulerProductRigidityStatement.{u} ∧
  HeckeLocalComponentRigidityStatement.{u}

end Langlands.Automorphic.Unramified
