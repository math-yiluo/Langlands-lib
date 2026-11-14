import Langlands.AllFieldBZ.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.Geometric.FlattenedLevi

/-!
# All-field port of `Langlands.Representation.Geometric.FlattenedLevi`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.FlattenedLevi` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric
open Langlands.GeneralLinear
universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

private theorem _root_.Langlands.Geometric.nestedLeviEmbedding_apply_ne (m : ∀ i, (S i).Levi R)
    (q q' : (i : Fin B.length) × Fin (S i).length) (hq : q ≠ q')
    (a : Fin ((S q.1).size q.2)) (b : Fin ((S q'.1).size q'.2)) :
    B.leviEmbedding R (fun i => (S i).leviEmbedding R (m i))
      (B.index q.1 ((S q.1).index q.2 a))
      (B.index q'.1 ((S q'.1).index q'.2 b)) = 0 := by
  rcases q with ⟨i, j⟩
  rcases q' with ⟨i', j'⟩
  by_cases hi : i = i'
  · subst i'
    rw [B.leviEmbedding_apply_same]
    exact (S i).leviEmbedding_apply_ne R (m i) a b (fun h => hq (by cases h; rfl))
  · exact B.leviEmbedding_apply_ne R _ _ _ hi

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

end Topology
end Langlands.AllFieldBZ.Geometric
