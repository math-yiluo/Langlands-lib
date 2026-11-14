import Langlands.AllFieldBZ.Representation.Geometric.BruhatMatrixStatement
import Langlands.Representation.Geometric.BruhatWeylReflectionProof

/-!
# All-field port of `Langlands.Representation.Geometric.BruhatWeylReflectionProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.BruhatWeylReflectionProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem padicBruhatWeylReflection
open Langlands.GeneralLinear
universe u

variable {n : ℕ} {R : Type u} [CommRing R] [Nontrivial R]

private theorem _root_.Langlands.Geometric.exists_nonzero_permutation_term (g : GeneralLinear n R) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j, g (σ j) j ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply Matrix.GeneralLinearGroup.det_ne_zero g
  rw [Matrix.det_apply']
  apply Finset.sum_eq_zero
  intro σ _
  obtain ⟨j, hj⟩ := h σ
  have hz : ∏ i : Fin n, g (σ i) i = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hj
  simp [hz]

omit [Nontrivial R] in
private theorem _root_.Langlands.Geometric.blockIndex_le_of_entry_ne_zero (B : BlockShape n)
    {g : GeneralLinear n R} (hg : g ∈ B.parabolic R) {i j : Fin n}
    (hij : g i j ≠ 0) : blockIndex B i ≤ blockIndex B j := by
  by_contra h
  have hz := (B.mem_parabolic_iff R g).mp hg
    (blockIndex B i) (blockIndex B j)
    (B.indexEquiv.symm i).2 (B.indexEquiv.symm j).2 (lt_of_not_ge h)
  have hi : B.index (blockIndex B i) (B.indexEquiv.symm i).2 = i :=
    B.indexEquiv.apply_symm_apply i
  have hj : B.index (blockIndex B j) (B.indexEquiv.symm j).2 = j :=
    B.indexEquiv.apply_symm_apply j
  exact hij (by simpa only [hi, hj] using hz)

private theorem _root_.Langlands.Geometric.permuted_nat_eq_of_le {α : Type*} [Fintype α]
    (f : α → ℕ) (v w : Equiv.Perm α) (h : ∀ i, f (v i) ≤ f (w i)) :
    ∀ i, f (v i) = f (w i) := by
  classical
  have hs : ∑ i, f (v i) = ∑ i, f (w i) :=
    (Equiv.sum_comp v f).trans (Equiv.sum_comp w f).symm
  exact fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).mp hs i
    (Finset.mem_univ i)

/-- The exact published p-adic reflection proposition. -/
theorem padicBruhatWeylReflection : PadicBruhatWeylReflectionTheorem.{u} := by
  intro F n hn B C v w h
  exact weyl_doubleCoset_eq_of_inverse_permutation_eq B C h

end Langlands.AllFieldBZ.Geometric
