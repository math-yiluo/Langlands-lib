import Langlands.ClassFieldTheory.Local.OpenFiniteIndexSeparationProof
import Langlands.ClassFieldTheory.Local.UniversalNormDivisibility
import Langlands.ClassFieldTheory.Local.NormExistenceUniversalLift

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- Containment of universal norms in every finite-index subgroup combines
with actual topological separation to give actual norm separation. -/
theorem normSubgroupsSeparatePoints_of_universalNorm_le_finiteIndex
    (hContain : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
      (H : Subgroup F.Carrierˣ), H.FiniteIndex →
        universalNormSubgroup F.Carrier ≤ H) :
    NormSubgroupsSeparatePoints.{u} := by
  intro p hp F a ha
  obtain ⟨H, _, hIndex, haH⟩ :=
    F.canonicalTopologicalData.exists_open_finiteIndex_excluding a ha
  have haU : a ∉ universalNormSubgroup F.Carrier :=
    fun h => haH (hContain p F H hIndex h)
  by_contra! h
  apply haU
  intro E hfd hAb
  exact h E hfd hAb

/-- The exact arithmetic inputs still needed by the universal-norm route. -/
theorem normSubgroupsSeparatePoints_of_universalNormLifting
    (hLift : UniversalNormLifting.{u})
    (hdir : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
      DirectedOn (· ≥ ·) (finiteAbelianNormFamily F.Carrier))
    (hclosed : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
      letI := F.canonicalTopologicalData.topology
      ∀ N ∈ finiteAbelianNormFamily F.Carrier, IsClosed (N : Set F.Carrierˣ)) :
    NormSubgroupsSeparatePoints.{u} := by
  apply normSubgroupsSeparatePoints_of_universalNorm_le_finiteIndex
  intro p hp F H hIndex
  let := hIndex
  exact ClassFieldTheory.Local.universalNorm_le_finiteIndex_of_lifting
    hLift F F.canonicalTopologicalData (hdir p F) (hclosed p F) H

/-- Every nonidentity field unit is excluded by the actual norm subgroup
of a finite abelian intermediate extension. -/
theorem normSubgroupsSeparatePoints : NormSubgroupsSeparatePoints.{u} := by
  apply normSubgroupsSeparatePoints_of_universalNormLifting
    ClassFieldTheory.Local.universalNormLifting
  · intro p hp F
    exact ClassFieldTheory.Local.finiteAbelianNormFamily_directed F.Carrier
  · intro p hp F
    exact ClassFieldTheory.Local.isClosed_finiteAbelianNormFamily
      F F.canonicalTopologicalData

end Langlands.LocalClassField
