import Langlands.Representation.Conductor.PrincipalCongruence

/-!
# Entrywise principal congruence and positive-level cofinality

These are proposition-valued targets for the existing actual principal
congruence subgroups, with the supplied field topology and valuation.
-/

open Matrix Filter Topology

namespace Langlands.Conductor

universe u

/-- Membership in the actual field subgroup is identity congruence for both
matrix entries and inverse-matrix entries, including at the unit ideal. -/
def PrincipalCongruenceEntryStatement : Prop :=
  ∀ (k : Type u) [Field k] (O : Subring k) (n : ℕ) (I : Ideal O)
    (g : GeneralLinearGroup (Fin (n + 1)) k),
    g ∈ principalCongruenceSubgroup O n I ↔
      (∀ i j : Fin (n + 1), ∃ x : O, x ∈ I ∧
        (x : k) = g i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j) ∧
      (∀ i j : Fin (n + 1), ∃ x : O, x ∈ I ∧
        (x : k) = g⁻¹ i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j)

/-- Positive principal levels are cofinal in the identity neighborhoods of the
actual general linear group over the supplied nonarchimedean local field. -/
def PrincipalLevelCofinalStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ)
    (U : Set (GeneralLinearGroup (Fin (n + 1)) k)),
    U ∈ 𝓝 (1 : GeneralLinearGroup (Fin (n + 1)) k) →
      ∃ a : ℕ, 0 < a ∧
        (principalLevelOpenSubgroup k n a : Set (GeneralLinearGroup (Fin (n + 1)) k)) ⊆ U

/-- The two-sided entry criterion and positive principal-level neighborhood API. -/
def PrincipalCongruenceBasisStatement : Prop :=
  PrincipalCongruenceEntryStatement.{u} ∧ PrincipalLevelCofinalStatement.{u}

end Langlands.Conductor
