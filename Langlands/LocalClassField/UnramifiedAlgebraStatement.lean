import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Norm.Defs

/-!
# Finite-level norms in an unramified finite free local algebra

These proposition definitions use the actual determinant norm and maximal-ideal
powers. They do not assert proofs or supply norm or trace surjectivity as data.
-/

namespace Langlands.LocalClassField.UnramifiedAlgebra

universe u v

/-- The determinant norm preserves every unit congruence level, including zero. -/
def NormPreservesUnitCongruences
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] : Prop :=
  ∀ (n : ℕ) (x : Sˣ),
    (x : S) - 1 ∈ (IsLocalRing.maximalIdeal S) ^ n →
      Algebra.norm R (x : S) - 1 ∈ (IsLocalRing.maximalIdeal R) ^ n

/-- Every unit at level `n` is a norm modulo level `n + 1`, with a preimage
unit at level `n`. Level zero is included. -/
def NormApproximatesUnitCongruences
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] : Prop :=
  ∀ (n : ℕ) (y : Rˣ),
    (y : R) - 1 ∈ (IsLocalRing.maximalIdeal R) ^ n →
      ∃ x : Sˣ,
        (x : S) - 1 ∈ (IsLocalRing.maximalIdeal S) ^ n ∧
          ((y * (Units.map (Algebra.norm R) x)⁻¹ : Rˣ) : R) - 1 ∈
            (IsLocalRing.maximalIdeal R) ^ (n + 1)

/-- Complete arithmetic proof target for finite free unramified local algebras
over a DVR with finite actual residue fields, in independent ring universes.
The equality of the mapped maximal ideal with the target maximal ideal is the
arithmetic unramified hypothesis. No completeness or Galois assumption is made. -/
def Statement : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain R] [IsDiscreteValuationRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Free R S] [Module.Finite R S]
    [Finite (IsLocalRing.ResidueField R)] [Finite (IsLocalRing.ResidueField S)],
    Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
        IsLocalRing.maximalIdeal S →
      NormPreservesUnitCongruences R S ∧
        NormApproximatesUnitCongruences R S

end Langlands.LocalClassField.UnramifiedAlgebra
