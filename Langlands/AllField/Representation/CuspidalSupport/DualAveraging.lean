import Langlands.Representation.CuspidalSupport.DualAveraging
import Langlands.AllField.Group.GL.BlockIwahoriBasis
import Langlands.AllField.Representation.CuspidalSupport.DeterminantUnit
/-!
# Averaging against smooth functionals, and compact open bases of product Levis

A functional that is smooth for the dual action is unchanged by first averaging
over any compact open subgroup fixing it. Product Levis and their determinant-unit
subgroups have neighbourhood bases of compact open subgroups.
-/

noncomputable section

open Filter Topology

namespace Langlands.AllField

universe uG uV uF

namespace Compact
open Langlands.Compact
open Langlands.AllField.Compact

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Compact

namespace CuspidalSupport
open Langlands.CuspidalSupport hiding continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal exists_leviPiOpenSubgroup_subset isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply leviPiOpenSubgroup levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_leviPiOpenSubgroup
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Geometric

variable {F : Type uF} [Field F] (T : LocalFieldData F)
  {n : ℕ} (B : BlockShape n)

/-- The product of open subgroups of the Levi factors, as an open subgroup. -/
def leviPiOpenSubgroup :
    letI := T.topology
    (∀ j, OpenSubgroup (GeneralLinear (B.size j) F)) → OpenSubgroup (B.Levi F) := by
  letI := T.topology
  exact fun K =>
    { toSubgroup := Subgroup.pi Set.univ fun j => (K j).toSubgroup
      isOpen' := by
        change IsOpen ((Subgroup.pi Set.univ fun j => (K j).toSubgroup :
          Subgroup (B.Levi F)) : Set (B.Levi F))
        rw [Subgroup.coe_pi]
        exact isOpen_set_pi Set.finite_univ fun j _ => (K j).isOpen }

theorem mem_leviPiOpenSubgroup :
    letI := T.topology
    ∀ (K : ∀ j, OpenSubgroup (GeneralLinear (B.size j) F)) (g : B.Levi F),
      g ∈ leviPiOpenSubgroup T B K ↔ ∀ j, g j ∈ K j := by
  let := T.topology
  intro K g
  change g ∈ Subgroup.pi Set.univ (fun j => (K j).toSubgroup) ↔ _
  rw [Subgroup.mem_pi]
  simp

theorem isCompact_leviPiOpenSubgroup :
    letI := T.topology
    ∀ (K : ∀ j, OpenSubgroup (GeneralLinear (B.size j) F)),
      (∀ j, IsCompact (K j : Set (GeneralLinear (B.size j) F))) →
      IsCompact (leviPiOpenSubgroup T B K : Set (B.Levi F)) := by
  let := T.topology
  intro K hK
  change IsCompact ((Subgroup.pi Set.univ fun j => (K j).toSubgroup :
    Subgroup (B.Levi F)) : Set (B.Levi F))
  rw [Subgroup.coe_pi]
  exact isCompact_univ_pi hK

/-- Every identity neighbourhood of the product Levi contains a product of compact
open subgroups, each with a block Iwahori factorization for the given refinement. -/
theorem exists_leviPiOpenSubgroup_subset (S : BlockRefinement B) :
    letI := T.topology
    ∀ {U : Set (B.Levi F)}, U ∈ 𝓝 (1 : B.Levi F) →
      ∃ K : ∀ j, OpenSubgroup (GeneralLinear (B.size j) F),
        (∀ j, IsCompact (K j : Set (GeneralLinear (B.size j) F))) ∧
        (∀ j, (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization (S j)) T (K j)) ∧
        (leviPiOpenSubgroup T B K : Set (B.Levi F)) ⊆ U := by
  let := T.topology
  intro U hU
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, O, hO, hOU⟩ := hU
  choose K hKc hKO hfac using fun j => (Langlands.AllField.GeneralLinear.BlockShape.blockIwahoriBasis (S j)) T (O j) (hO j)
  refine ⟨K, hKc, hfac, ?_⟩
  intro g hg
  apply hOU
  intro j _
  exact hKO j ((mem_leviPiOpenSubgroup T B K g).mp hg j)

/-- Compact open subgroups form a neighbourhood basis of `1` in the product Levi. -/
theorem levi_exists_compact_openSubgroup_subset :
    letI := T.topology
    ∀ U ∈ 𝓝 (1 : B.Levi F), ∃ K : OpenSubgroup (B.Levi F),
      IsCompact (K : Set (B.Levi F)) ∧ (K : Set (B.Levi F)) ⊆ U := by
  let := T.topology
  intro U hU
  let S : BlockRefinement B := fun j =>
    { length := 1
      size := fun _ => B.size j
      positive := fun _ => B.positive j
      sum_eq := by simp }
  obtain ⟨K, hKc, -, hKU⟩ := exists_leviPiOpenSubgroup_subset T B S hU
  exact ⟨leviPiOpenSubgroup T B K, isCompact_leviPiOpenSubgroup T B K hKc, hKU⟩

end CuspidalSupport

end Langlands.AllField
