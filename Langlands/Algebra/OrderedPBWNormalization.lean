import Langlands.Algebra.OrderedPBWCoherence

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping.PBW

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
variable {n : ℕ} (b : Module.Basis (Fin n) k L)

/-- The linear normal form obtained from adjacent-inversion Lie-word reduction. -/
def normalForm : Module.End k (WordModule k n) :=
  TriangularNormalization.normalize WordLT wordLT_wf (Reduction b)

theorem normalForm_rule {w : List (Fin n)} {p : WordModule k n}
    (hp : Reduction b w p) :
    normalForm b (Finsupp.single w 1) = normalForm b p := by
  simpa only [normalForm, TriangularNormalization.normalize_single, one_smul] using
    TriangularNormalization.normalizeWord_rule WordLT wordLT_wf (Reduction b)
      (reduction_triangular b) (reduction_coherent b) w p hp

theorem normalForm_respects (w : List (Fin n)) :
    RespectsBelow b w (normalForm b) :=
  fun _ _ _ hp => normalForm_rule b hp

theorem normalForm_ascending (w : List (Fin n)) (hw : w.Pairwise (· ≤ ·)) :
    normalForm b (Finsupp.single w 1) = Finsupp.single w 1 := by
  simpa only [normalForm, TriangularNormalization.normalize_single, one_smul] using
    TriangularNormalization.normalizeWord_irreducible WordLT wordLT_wf (Reduction b)
      ((irreducible_iff_pairwise b w).mpr hw)

theorem normalForm_supported (p : WordModule k n) :
    normalForm b p ∈ Finsupp.supported k k {w | w.Pairwise (· ≤ ·)} := by
  have h := TriangularNormalization.normalize_mem_supported WordLT wordLT_wf
    (Reduction b) (reduction_triangular b) p
  simpa only [normalForm, irreducible_iff_pairwise] using h

theorem ker_normalForm :
    LinearMap.ker (normalForm b) = TriangularNormalization.relations (Reduction b) :=
  TriangularNormalization.ker_normalize WordLT wordLT_wf (Reduction b)
    (reduction_triangular b) (reduction_coherent b)

theorem prepend_relations (i : Fin n) {p : WordModule k n}
    (hp : p ∈ TriangularNormalization.relations (Reduction b)) :
    prepend i p ∈ TriangularNormalization.relations (Reduction b) := by
  have h : TriangularNormalization.relations (Reduction b) ≤
      (TriangularNormalization.relations (Reduction b)).comap (prepend i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, q, hq, rfl⟩
    change prepend i (Finsupp.single w 1 - q) ∈
      TriangularNormalization.relations (Reduction b)
    rw [map_sub, prepend_single]
    exact Submodule.subset_span ⟨_, _, Reduction.cons i hq, rfl⟩
  exact h hp

theorem insert_relations (x : L) {p : WordModule k n}
    (hp : p ∈ TriangularNormalization.relations (Reduction b)) :
    insert b x p ∈ TriangularNormalization.relations (Reduction b) := by
  classical
  rw [insert_apply]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (prepend_relations b i hp)

theorem normalForm_insert_normalForm (x : L) (p : WordModule k n) :
    normalForm b (insert b x (normalForm b p)) = normalForm b (insert b x p) := by
  have h := insert_relations b x
    (TriangularNormalization.sub_normalize_mem_relations WordLT wordLT_wf
      (Reduction b) (reduction_triangular b) p)
  rw [← ker_normalForm] at h
  change normalForm b (insert b x (p - normalForm b p)) = 0 at h
  simp only [map_sub, sub_eq_zero] at h
  exact h.symm

theorem normalForm_insert_basis_pair (x : L) (j : Fin n) (p : WordModule k n) :
    normalForm b (insert b x (prepend j p)) =
      normalForm b (prepend j (insert b x p)) +
        normalForm b (insert b ⁅x, b j⁆ p) := by
  let A : Module.End k (WordModule k n) :=
    (normalForm b).comp ((insert b x).comp (prepend j))
  let B : Module.End k (WordModule k n) :=
    (normalForm b).comp (((prepend j).comp (insert b x)) + insert b ⁅x, b j⁆)
  suffices A p = B p by
    simpa only [A, B, LinearMap.comp_apply, LinearMap.add_apply, map_add] using this
  apply linear_eq_of_support A B p
  intro s hs
  have h := respects_insert_pair_of_length b (j :: j :: j :: s) (normalForm b)
    (normalForm_respects b _) x j s (by simp)
  simpa only [A, B, LinearMap.comp_apply, LinearMap.add_apply, map_add] using h

theorem normalForm_insert_pair (x y : L) (p : WordModule k n) :
    normalForm b (insert b x (insert b y p)) =
      normalForm b (insert b y (insert b x p)) +
        normalForm b (insert b ⁅x, y⁆ p) := by
  classical
  rw [← b.sum_repr y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    lie_sum, lie_smul, insert_basis]
  simp_rw [normalForm_insert_basis_pair b x _ p]
  simp only [smul_add, Finset.sum_add_distrib]

end Langlands.Algebra.UniversalEnveloping.PBW
