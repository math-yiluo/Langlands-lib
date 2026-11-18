import Langlands.Correspondence.HenniartNumericalStatement
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Divisors

/-!
# Refined orbit strata for Henniart's numerical correspondence

Swan exponents, unramified-twist stabilizer sizes, refined orbit counts and
the counting-versus-surjectivity proposition of the operator route note,
§§2.2–2.3 and §6.1. Definitions and proposition targets only.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uW uV

namespace Numerical

open Langlands.Correspondence Langlands.VirtualRepresentation
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Swan exponent obtained by truncated subtraction of the rank from a
natural Artin conductor; this also covers unramified rank-one classes. -/
def HasWeilSwan {k : ℕ} (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat)
    (s : ℕ) : Prop :=
  ∃ a : ℕ, HasArtinConductor K σ a ∧ a - (k + 1) = s

/-- Swan exponent obtained by truncated subtraction of the rank from a
finite supercuspidal conductor. -/
def HasSupercuspidalSwan {k : ℕ}
    (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) (s : ℕ) : Prop :=
  ∃ a : ℕ, conductor K π = (a : WithTop ℕ) ∧ a - (k + 1) = s

/-- Cardinality of the unramified-twist stabilizer of a Weil class. -/
def weilTorsionNumber {k : ℕ} (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) : ℕ :=
  Nat.card {z : ℂˣ // weilUnramifiedTwist K k z σ = σ}

/-- Cardinality of the unramified-twist stabilizer of a supercuspidal class. -/
def supercuspidalTorsionNumber {k : ℕ}
    (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) : ℕ :=
  Nat.card {z : ℂˣ // supercuspidalUnramifiedTwist K k z π = π}

/-- `W_K(k+1,s,f)`: unramified-twist orbits containing a Weil class of the
given rank, Swan exponent and torsion number. -/
def weilRefinedStratum (k s f : ℕ) :
    Set (Weil.UnramifiedOrbitClasses.{uK, uW} (Weil.Local.localDegree K)) :=
  {c | ∃ σ : IrreducibleWeilClass.{uK, uW} K k.succPNat,
    Weil.unramifiedOrbitClass (Weil.Local.localDegree K) ⟨k.succPNat, σ⟩ = c ∧
      HasWeilSwan K σ s ∧ weilTorsionNumber K σ = f}

/-- `S_K(k+1,s,f)`: unramified-twist orbits containing a supercuspidal class
of the given rank, Swan exponent and torsion number. -/
def supercuspidalRefinedStratum (k s f : ℕ) :
    Set (PadicSupercuspidal.UnramifiedOrbitClasses.{uK, uV} K) :=
  {c | ∃ π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat,
    PadicSupercuspidal.unramifiedOrbitClass K ⟨k.succPNat, π⟩ = c ∧
      HasSupercuspidalSwan K π s ∧ supercuspidalTorsionNumber K π = f}

/-- `T_K(k+1,s)`, the extended natural count of torsion-number-one Weil orbits. -/
def weilTwistIrreducibleCount (k s : ℕ) : ℕ∞ :=
  (weilRefinedStratum.{uK, uW} K k s 1).encard

/-- Henniart's `C_K(k+1,j)`: sum over `d ∣ k+1` and
`0 ≤ s ≤ d*j/(k+1)`, including Swan exponent zero. -/
def weilConductorCount (k j : ℕ) : ℕ∞ :=
  ∑ d ∈ (k + 1).divisors,
    ∑ s ∈ Finset.range (d * j / (k + 1) + 1),
      weilTwistIrreducibleCount.{uK, uW} K (d - 1) s

/-- `C(K,x,N)`: equal refined counts and finite supercuspidal strata in
ranks at most `N` and at slopes at most the real number `x`. -/
def CountsAgreeUpToSlope (x : ℝ) (N : ℕ) : Prop :=
  ∀ (k s f : ℕ), k + 1 ≤ N → (s : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * x →
    (weilRefinedStratum.{uK, uW} K k s f).encard =
        (supercuspidalRefinedStratum.{uK, uV} K k s f).encard ∧
      (supercuspidalRefinedStratum.{uK, uV} K k s f).Finite

end Numerical

open Numerical Correspondence

/-- Every irreducible Weil class over a p-adic field has a natural Artin
conductor. The integrality input is Serre, Local Fields, VI §2, Theorem 1′. -/
def WeilArtinConductorExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat),
    ∃ a : ℕ, HasArtinConductor K σ a

/-- A numerical injection preserves torsion numbers and Swan exponents
and gives the inequality between every pair of refined orbit counts. -/
def NumericalInjectionRefinedStrataStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
    (φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
      SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat),
    IsNumericalInjection K φ →
      (∀ σ, supercuspidalTorsionNumber K (φ σ) = weilTorsionNumber K σ) ∧
      (∀ σ s, HasWeilSwan K σ s → HasSupercuspidalSwan K (φ σ) s) ∧
      ∀ s f, (weilRefinedStratum.{uK, uW} K k s f).encard ≤
        (supercuspidalRefinedStratum.{uK, uV} K k s f).encard

/-- Counting versus surjectivity (route note, Lemma `lem:countsurj`).
The converse explicitly assumes natural Artin conductors in ranks at most `N`. -/
def CountingSurjectivityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (x : ℝ) (N : ℕ),
    (CountsAgreeUpToSlope.{uK, uW, uV} K x N →
      ∀ (k : ℕ), k + 1 ≤ N →
        ∀ (φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
          SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat),
          IsNumericalInjection K φ →
            ∀ (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) (s : ℕ),
              HasSupercuspidalSwan K π s → (s : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * x →
                π ∈ Set.range φ) ∧
    ((∀ (k : ℕ), k + 1 ≤ N →
        ∀ (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat),
          ∃ a : ℕ, HasArtinConductor K σ a) →
      (∀ (k : ℕ), k + 1 ≤ N →
        ∃ φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
            SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat,
          IsNumericalInjection K φ ∧
            ∀ (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) (s : ℕ),
              HasSupercuspidalSwan K π s → (s : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * x →
                π ∈ Set.range φ) →
      CountsAgreeUpToSlope.{uK, uW, uV} K x N)

/-- The refined-strata preservation and counting-versus-surjectivity package. -/
def RefinedStrataStatement : Prop :=
  NumericalInjectionRefinedStrataStatement.{uK, uW, uV} ∧
    CountingSurjectivityStatement.{uK, uW, uV}

end Langlands.Henniart
