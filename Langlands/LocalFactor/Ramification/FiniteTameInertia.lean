import Langlands.LocalFactor.Ramification.Galois
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The finite tame inertia quotient

Serre, *Local Fields*, IV §2, Proposition 7 and Corollaries 1 and 3.
-/

noncomputable section

namespace Langlands.Ramification.Padic

universe uK uL

section Quotient

variable {p : ℕ} [Fact p.Prime] {L : PadicField.{uL} p} (T : L.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K] [Algebra K L.Carrier]
  [IsScalarTower (Padic p) K L.Carrier]

/-- The first lower group, viewed inside inertia, the zeroth lower group. -/
abbrev finiteWildInInertia : Subgroup (lowerRamificationGroup T K 0) :=
  (lowerRamificationGroup T K 1).subgroupOf (lowerRamificationGroup T K 0)

/-- The tame quotient of the actual finite inertia group. -/
abbrev finiteTameInertiaQuotient := (lowerRamificationGroup T K 0) ⧸ finiteWildInInertia T K

end Quotient

/-- Wild inertia in a finite Galois extension of p-adic fields is a p-group.
The tame inertia quotient admits an injective residue-field character, is
cyclic, and has order dividing the residue unit-group order and prime to `p`. -/
def FiniteTameInertiaStructureStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (L : PadicField.{uL} p)
    [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
    [FiniteDimensional K.Carrier L.Carrier] [IsGalois K.Carrier L.Carrier]
    (T : L.TopologicalData),
    IsPGroup p (lowerRamificationGroup T K.Carrier 1) ∧
      (∃ θ : finiteTameInertiaQuotient T K.Carrier →* T.ResidueFieldˣ, Function.Injective θ) ∧
      IsCyclic (finiteTameInertiaQuotient T K.Carrier) ∧
      Nat.card (finiteTameInertiaQuotient T K.Carrier) ∣ T.residueCardinality - 1 ∧
      p.Coprime (Nat.card (finiteTameInertiaQuotient T K.Carrier))

end Langlands.Ramification.Padic
