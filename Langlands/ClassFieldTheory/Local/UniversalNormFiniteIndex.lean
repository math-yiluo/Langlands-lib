import Langlands.ClassFieldTheory.Local.NormExistenceUniversalLift

/-! # Unconditional divisibility and finite-index containment of universal norms -/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- Every actual finite-index subgroup contains all universal norms. -/
def UniversalNormFiniteIndexContainment : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (H : Subgroup F.Carrierˣ) [H.FiniteIndex],
    universalNormSubgroup F.Carrier ≤ H

end Langlands.LocalClassField

namespace Langlands.ClassFieldTheory.Local

universe u

open Langlands.LocalClassField

variable {p : ℕ} [Fact p.Prime]

/-- Every universal norm has prime roots within the universal norm subgroup. -/
theorem universalNorm_prime_root_mem
    (F : PadicField.{u} p) {q : ℕ} (hq : q.Prime) (a : F.Carrierˣ)
    (ha : a ∈ universalNormSubgroup F.Carrier) :
    ∃ b : F.Carrierˣ, b ∈ universalNormSubgroup F.Carrier ∧ b ^ q = a :=
  universalNorm_prime_root_mem_of_lifting universalNormLifting F F.canonicalTopologicalData
    (finiteAbelianNormFamily_directed F.Carrier)
    (isClosed_finiteAbelianNormFamily F F.canonicalTopologicalData) hq a ha

/-- Every universal norm has roots of every positive natural order inside
the universal norm subgroup. -/
theorem universalNorm_all_roots (F : PadicField.{u} p) :
    ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ universalNormSubgroup F.Carrier,
      ∃ b : F.Carrierˣ, b ∈ universalNormSubgroup F.Carrier ∧ b ^ n = a :=
  universalNorm_all_roots_of_lifting universalNormLifting F F.canonicalTopologicalData
    (finiteAbelianNormFamily_directed F.Carrier)
    (isClosed_finiteAbelianNormFamily F F.canonicalTopologicalData)

/-- Universal norms lie in every finite-index subgroup of the actual
multiplicative group. -/
theorem universalNorm_le_finiteIndex
    (F : PadicField.{u} p) (H : Subgroup F.Carrierˣ) [H.FiniteIndex] :
    universalNormSubgroup F.Carrier ≤ H :=
  subgroup_le_finiteIndex_of_all_roots _ (universalNorm_all_roots F) H

/-- Finite-index containment holds without an additional arithmetic premise. -/
theorem universalNormFiniteIndexContainment : UniversalNormFiniteIndexContainment.{u} := by
  intro p hp F H hH
  exact universalNorm_le_finiteIndex F H

end Langlands.ClassFieldTheory.Local
