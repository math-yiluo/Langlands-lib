import Langlands.AllFieldBZ.Group.GL.BlockIwahoriBasis
import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.CuspidalSupport.DeterminantUnit
import Langlands.Representation.CuspidalSupport.DualAveraging

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.DualAveraging`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.DualAveraging` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open Filter
open Topology
namespace Langlands.AllFieldBZ
universe uG uV uF

namespace Compact
open Langlands.Compact
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Compact
namespace CuspidalSupport
open Langlands.CuspidalSupport hiding continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal exists_leviPiOpenSubgroup_subset isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply leviPiOpenSubgroup levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_leviPiOpenSubgroup
open Langlands.GeneralLinear
open Langlands.Geometric
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n)

/-- The product of open subgroups of the Levi factors, as an open subgroup. -/
def leviPiOpenSubgroup :
    letI := T.topology
    (∀ j, OpenSubgroup (GeneralLinear (B.size j) F.Carrier)) → OpenSubgroup (B.Levi F.Carrier) := by
  letI := T.topology
  exact fun K =>
    { toSubgroup := Subgroup.pi Set.univ fun j => (K j).toSubgroup
      isOpen' := by
        change IsOpen ((Subgroup.pi Set.univ fun j => (K j).toSubgroup :
          Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier))
        rw [Subgroup.coe_pi]
        exact isOpen_set_pi Set.finite_univ fun j _ => (K j).isOpen }

theorem mem_leviPiOpenSubgroup :
    letI := T.topology
    ∀ (K : ∀ j, OpenSubgroup (GeneralLinear (B.size j) F.Carrier)) (g : B.Levi F.Carrier),
      g ∈ leviPiOpenSubgroup T B K ↔ ∀ j, g j ∈ K j := by
  let := T.topology
  intro K g
  change g ∈ Subgroup.pi Set.univ (fun j => (K j).toSubgroup) ↔ _
  rw [Subgroup.mem_pi]
  simp

theorem isCompact_leviPiOpenSubgroup :
    letI := T.topology
    ∀ (K : ∀ j, OpenSubgroup (GeneralLinear (B.size j) F.Carrier)),
      (∀ j, IsCompact (K j : Set (GeneralLinear (B.size j) F.Carrier))) →
      IsCompact (leviPiOpenSubgroup T B K : Set (B.Levi F.Carrier)) := by
  let := T.topology
  intro K hK
  change IsCompact ((Subgroup.pi Set.univ fun j => (K j).toSubgroup :
    Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier))
  rw [Subgroup.coe_pi]
  exact isCompact_univ_pi hK

/-- Every identity neighbourhood of the product Levi contains a product of compact
open subgroups, each with a block Iwahori factorization for the given refinement. -/
theorem exists_leviPiOpenSubgroup_subset (S : BlockRefinement B) :
    letI := T.topology
    ∀ {U : Set (B.Levi F.Carrier)}, U ∈ 𝓝 (1 : B.Levi F.Carrier) →
      ∃ K : ∀ j, OpenSubgroup (GeneralLinear (B.size j) F.Carrier),
        (∀ j, IsCompact (K j : Set (GeneralLinear (B.size j) F.Carrier))) ∧
        (∀ j, (S j).HasBlockIwahoriFactorization_allFieldBZ T (K j)) ∧
        (leviPiOpenSubgroup T B K : Set (B.Levi F.Carrier)) ⊆ U := by
  let := T.topology
  intro U hU
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, O, hO, hOU⟩ := hU
  choose K hKc hKO hfac using fun j => (S j).blockIwahoriBasis_allFieldBZ T (O j) (hO j)
  refine ⟨K, hKc, hfac, ?_⟩
  intro g hg
  apply hOU
  intro j _
  exact hKO j ((mem_leviPiOpenSubgroup T B K g).mp hg j)

/-- Compact open subgroups form a neighbourhood basis of `1` in the product Levi. -/
theorem levi_exists_compact_openSubgroup_subset :
    letI := T.topology
    ∀ U ∈ 𝓝 (1 : B.Levi F.Carrier), ∃ K : OpenSubgroup (B.Levi F.Carrier),
      IsCompact (K : Set (B.Levi F.Carrier)) ∧ (K : Set (B.Levi F.Carrier)) ⊆ U := by
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
end Langlands.AllFieldBZ
