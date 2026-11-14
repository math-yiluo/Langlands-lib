import Langlands.AllFieldBZ.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.Group.GL.AdjacentMergeShape

/-!
# All-field port of `Langlands.Group.GL.AdjacentMergeShape`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.AdjacentMergeShape` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
variable {n : ℕ}

section Coordinates
variable (B D : Langlands.GeneralLinear.BlockShape n) (S : BlockRefinement D)
    (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
    (hs : ∀ a, (S a.1).size a.2 = B.size (e a))

end Coordinates
private theorem _root_.Langlands.GeneralLinear.BlockShape.sum_fin_of_eq_two (L : ℕ) (hL : L = 2) (f : Fin L → ℕ) :
    ∑ k, f k = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  subst hL
  exact Fin.sum_univ_two f

private theorem _root_.Langlands.GeneralLinear.BlockShape.sum_fin_of_eq_one (L : ℕ) (hL : L = 1) (f : Fin L → ℕ) :
    ∑ k, f k = f ⟨0, by omega⟩ := by
  subst hL
  exact Fin.sum_univ_one f

section Merge
variable (B : Langlands.GeneralLinear.BlockShape n) (j : ℕ) (h : j + 1 < B.length)

private theorem _root_.Langlands.GeneralLinear.BlockShape.sum_range_adjacent (m : ℕ) :
    ∑ i ∈ Finset.range m, (if i = j then 2 else 1) = m + if j < m then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

private theorem _root_.Langlands.GeneralLinear.BlockShape.sum_adjacentInnerLength_castLE (m : ℕ) (hm : m ≤ B.length - 1) :
    ∑ i : Fin m, B.adjacentInnerLength j (Fin.castLE hm i) = m + if j < m then 1 else 0 :=
  (Fin.sum_univ_eq_sum_range (fun i => if i = j then 2 else 1) m).trans
    (sum_range_adjacent j m)

/-! ### Explicit length and size laws -/

/-! ### The collapse of block labels -/

end Merge
section Swap
variable (B : Langlands.GeneralLinear.BlockShape n) (j : ℕ) (h : j + 1 < B.length)

end Swap
end Langlands.AllFieldBZ.GeneralLinear.BlockShape
