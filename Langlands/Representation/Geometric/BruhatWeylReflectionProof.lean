import Langlands.Representation.Geometric.BruhatMatrixStatement
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Reflection of Weyl double cosets using a nonzero determinant term. -/

namespace Langlands.Geometric

open GeneralLinear

universe u

variable {n : ℕ} {R : Type u} [CommRing R] [Nontrivial R]

private theorem exists_nonzero_permutation_term (g : GeneralLinear n R) :
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
private theorem blockIndex_le_of_entry_ne_zero (B : BlockShape n)
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

private theorem permuted_nat_eq_of_le {α : Type*} [Fintype α]
    (f : α → ℕ) (v w : Equiv.Perm α) (h : ∀ i, f (v i) ≤ f (w i)) :
    ∀ i, f (v i) = f (w i) := by
  classical
  have hs : ∑ i, f (v i) = ∑ i, f (w i) :=
    (Equiv.sum_comp v f).trans (Equiv.sum_comp w f).symm
  exact fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).mp hs i
    (Finset.mem_univ i)

/-- Equality of inverse permutation-matrix parabolic classes reflects Weyl
classes over every nontrivial commutative ring. -/
theorem weyl_doubleCoset_eq_of_inverse_permutation_eq (B C : BlockShape n)
    {v w : Equiv.Perm (Fin n)}
    (h : DoubleCoset.mk (B.parabolic R) (C.parabolic R) (permutation n R v)⁻¹ =
      DoubleCoset.mk (B.parabolic R) (C.parabolic R) (permutation n R w)⁻¹) :
    DoubleCoset.mk (blockWeyl C) (blockWeyl B) v =
      DoubleCoset.mk (blockWeyl C) (blockWeyl B) w := by
  classical
  obtain ⟨a, ha, b, hb, hv⟩ := DoubleCoset.eq.mp h.symm
  have he : a = (permutation n R v)⁻¹ * b⁻¹ * permutation n R w := by
    rw [hv]
    group
  obtain ⟨σ, hσ⟩ := exists_nonzero_permutation_term a
  have hB : ∀ j, blockIndex B (σ j) = blockIndex B j := by
    intro j
    apply Fin.ext
    exact permuted_nat_eq_of_le (fun j => (blockIndex B j).val) σ 1
      (fun j => blockIndex_le_of_entry_ne_zero B ha (hσ j)) j
  have hC_le : ∀ j, blockIndex C (v (σ j)) ≤ blockIndex C (w j) := by
    intro j
    apply blockIndex_le_of_entry_ne_zero C ((C.parabolic R).inv_mem hb)
    have hz := hσ j
    rw [he, mul_permutation_entry, permutation_inv, permutation_mul_entry,
      inv_inv] at hz
    exact hz
  have hC : ∀ j, blockIndex C (v (σ j)) = blockIndex C (w j) := by
    intro j
    apply Fin.ext
    exact permuted_nat_eq_of_le (fun j => (blockIndex C j).val) (v * σ) w
      hC_le j
  apply Eq.symm
  apply DoubleCoset.eq.mpr
  refine ⟨v * σ * w⁻¹, ?_, σ⁻¹, (blockWeyl B).inv_mem hB, ?_⟩
  · intro i
    change blockIndex C (v (σ (w⁻¹ i))) = blockIndex C i
    simpa using hC (w⁻¹ i)
  · group

/-- The exact published p-adic reflection proposition. -/
theorem padicBruhatWeylReflection : PadicBruhatWeylReflectionTheorem.{u} := by
  intro p hp F n hn B C v w h
  exact weyl_doubleCoset_eq_of_inverse_permutation_eq B C h

end Langlands.Geometric
