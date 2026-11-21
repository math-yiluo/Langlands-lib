import Langlands.LocalFactor.Ramification.InertiaPresentation
import Langlands.VirtualRepresentation.Weil.Twist
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Divisors

/-! # Weil-side numerical invariants of nonarchimedean local fields -/

noncomputable section

namespace Langlands.Henniart.LocalNumerical

open Langlands.VirtualRepresentation
open scoped BigOperators

universe uK uΩ uW

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local notation "W" =>
  (@Weil.Local.SepClosed.localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

local notation "degree" =>
  (@Weil.Local.SepClosed.localDegree K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

local notation "unramifiedCharacter" =>
  (@Weil.Local.SepClosed.localUnramifiedCharacter K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

/-- Rank-`n` isomorphism classes of continuous irreducible complex Weil representations. -/
abbrev IrreducibleWeilClass (n : ℕ+) :=
  FiniteRepresentation.ContinuousIrreducibleClasses.{uΩ, uW} W (n : ℕ)

/-- The underlying representation class, forgetting continuity, irreducibility and rank. -/
abbrev weilClassForget {n : ℕ+} (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω n) :
    FiniteRepresentation.IsomorphismClasses.{0, uΩ, uW} ℂ W :=
  FiniteRepresentation.forgetPropertyClass
    (fun A : FiniteRepresentation.{0, uΩ, uW} ℂ W =>
      A.IsContinuous ∧ A.IsIrreducible) σ.val

/-- Some representative of `σ` has the given Artin exponent at a finite inertia
presentation with surjective inertia restriction. -/
def HasArtinConductor {k : ℕ} (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat)
    (a : ℕ) : Prop :=
  ∃ (A : FiniteRepresentation.{0, uΩ, uW} ℂ W)
    (P : Ramification.Local.SepClosed.FiniteInertiaPresentation K Ω A)
    (hsurj : Function.Surjective (Ramification.Local.SepClosed.weilInertiaRestriction K Ω P.extension)),
    FiniteRepresentation.classOf A = weilClassForget K Ω σ ∧
      Ramification.Local.SepClosed.FiniteInertiaPresentation.artinConductor P hsurj = (a : ℚ)

/-- Twist by the unramified character sending geometric Frobenius to `z`. -/
def weilUnramifiedTwist (k : ℕ) (z : ℂˣ) :
    IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat ≃
      IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat :=
  FiniteRepresentation.continuousIrreducibleTwistEquiv (unramifiedCharacter z) (k + 1)

/-- Unramified-twist orbits containing a rank-`k + 1` class of Artin conductor `a`. -/
def weilOrbitStratum (k a : ℕ) :
    Set (Weil.UnramifiedOrbitClasses.{uΩ, uW} degree) :=
  {c | ∃ σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat,
    Weil.unramifiedOrbitClass degree ⟨k.succPNat, σ⟩ = c ∧
      HasArtinConductor K Ω σ a}

/-- The Swan exponent obtained by subtracting the rank from the Artin exponent in `ℕ`. -/
def HasWeilSwan {k : ℕ} (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat)
    (s : ℕ) : Prop :=
  ∃ a : ℕ, HasArtinConductor K Ω σ a ∧ a - (k + 1) = s

/-- The natural cardinality of the unramified-twist stabilizer of a Weil class. -/
def weilTorsionNumber {k : ℕ} (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) : ℕ :=
  Nat.card {z : ℂˣ // weilUnramifiedTwist K Ω k z σ = σ}

/-- `W_K(k+1,s,f)`, the twist orbits containing a class of the given rank,
Swan exponent and torsion number. -/
def weilRefinedStratum (k s f : ℕ) :
    Set (Weil.UnramifiedOrbitClasses.{uΩ, uW} degree) :=
  {c | ∃ σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat,
    Weil.unramifiedOrbitClass degree ⟨k.succPNat, σ⟩ = c ∧
      HasWeilSwan K Ω σ s ∧ weilTorsionNumber K Ω σ = f}

/-- `T_K(k+1,s)`, the extended natural count of torsion-number-one Weil orbits. -/
def weilTwistIrreducibleCount (k s : ℕ) : ℕ∞ :=
  (weilRefinedStratum.{uK, uΩ, uW} K Ω k s 1).encard

/-- `C_K(k+1,j)`, summing `T_K(d,s)` for divisors `d` of `k+1` and
Swan exponents `s` with `(k+1)*s ≤ d*j`, including zero. -/
def weilConductorCount (k j : ℕ) : ℕ∞ :=
  ∑ d ∈ (k + 1).divisors,
    ∑ s ∈ Finset.range (d * j / (k + 1) + 1),
      weilTwistIrreducibleCount.{uK, uΩ, uW} K Ω (d - 1) s

end Langlands.Henniart.LocalNumerical
