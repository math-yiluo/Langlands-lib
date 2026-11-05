import Langlands.GroupScheme.SplitExistence.IntegralBase
import Mathlib.Data.Int.Interval

/-!
# Minimal-norm weights in a coset of the root lattice

For a finite root datum `P` with weight lattice `X`, the canonical form
`RootPairing.RootForm` takes nonnegative integer values on the diagonal. In a coset
`w + ℤΦ` the elements of minimal norm pair with every coroot to `-1`, `0` or `1`; they form a
finite set that is stable under every reflection.
-/

namespace Langlands.GroupScheme.SplitExistence

open RootPairing Set

variable {J X Y : Type*} [Fintype J] [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y)

lemma rootForm_sub_root (x : X) (j : J) :
    P.RootForm (x - P.root j) (x - P.root j) =
      P.RootForm x x - (P.toLinearMap x (P.coroot j) - 1) *
        P.RootForm (P.root j) (P.root j) := by
  have h := two_mul_rootForm_root P x j
  have hc := rootForm_comm P (P.root j) x
  simp only [map_sub, LinearMap.sub_apply]
  linear_combination -hc - h

lemma rootForm_add_root (x : X) (j : J) :
    P.RootForm (x + P.root j) (x + P.root j) =
      P.RootForm x x + (P.toLinearMap x (P.coroot j) + 1) *
        P.RootForm (P.root j) (P.root j) := by
  have h := two_mul_rootForm_root P x j
  have hc := rootForm_comm P (P.root j) x
  simp only [map_add, LinearMap.add_apply]
  linear_combination hc + h

open scoped Classical in
/-- The minimal value of the canonical norm on the coset `w + ℤΦ`. -/
noncomputable def minNorm (w : X) : ℕ :=
  Nat.find (p := fun n : ℕ ↦ ∃ q ∈ P.rootSpan ℤ, P.RootForm (w + q) (w + q) = n)
    ⟨(P.RootForm w w).toNat, 0, zero_mem _, by
      simpa using (Int.toNat_of_nonneg (rootForm_self_nonneg P w)).symm⟩

lemma exists_minNorm (w : X) :
    ∃ q ∈ P.rootSpan ℤ, P.RootForm (w + q) (w + q) = minNorm P w := by
  classical
  exact Nat.find_spec (p := fun n : ℕ ↦ ∃ q ∈ P.rootSpan ℤ, P.RootForm (w + q) (w + q) = n) _

lemma minNorm_le {w ν : X} (h : ν - w ∈ P.rootSpan ℤ) :
    (minNorm P w : ℤ) ≤ P.RootForm ν ν := by
  classical
  have hle : minNorm P w ≤ (P.RootForm ν ν).toNat :=
    Nat.find_min' (p := fun n : ℕ ↦ ∃ q ∈ P.rootSpan ℤ, P.RootForm (w + q) (w + q) = n) _
      ⟨ν - w, h, by
        simpa using (Int.toNat_of_nonneg (rootForm_self_nonneg P ν)).symm⟩
  have := Int.toNat_of_nonneg (rootForm_self_nonneg P ν)
  omega

/-- The elements of minimal canonical norm in the coset `w + ℤΦ`. -/
def minimalWeights (w : X) : Set X :=
  {ν | ν - w ∈ P.rootSpan ℤ ∧ P.RootForm ν ν = minNorm P w}

variable {P}

omit [Fintype J] in
lemma root_mem_rootSpan (j : J) : P.root j ∈ P.rootSpan ℤ :=
  Submodule.subset_span (mem_range_self j)

lemma minimalWeights_nonempty (w : X) : (minimalWeights P w).Nonempty := by
  obtain ⟨q, hq, h⟩ := exists_minNorm P w
  exact ⟨w + q, by simpa using hq, h⟩

lemma pairing_le_one {w ν : X} (hν : ν ∈ minimalWeights P w) (j : J) :
    P.toLinearMap ν (P.coroot j) ≤ 1 := by
  by_contra! hlt
  have hmem : ν - P.root j - w ∈ P.rootSpan ℤ := by
    have := sub_mem hν.1 (root_mem_rootSpan (P := P) j)
    rwa [sub_right_comm] at this
  have h1 := minNorm_le P hmem
  have h2 := rootForm_sub_root P ν j
  have h3 := four_le_rootForm_root P j
  rw [hν.2] at h2
  nlinarith

lemma neg_one_le_pairing {w ν : X} (hν : ν ∈ minimalWeights P w) (j : J) :
    -1 ≤ P.toLinearMap ν (P.coroot j) := by
  by_contra! hlt
  have hmem : ν + P.root j - w ∈ P.rootSpan ℤ := by
    have := add_mem hν.1 (root_mem_rootSpan (P := P) j)
    rwa [sub_add_eq_add_sub] at this
  have h1 := minNorm_le P hmem
  have h2 := rootForm_add_root P ν j
  have h3 := four_le_rootForm_root P j
  rw [hν.2] at h2
  nlinarith

lemma reflection_mem_minimalWeights {w ν : X} (hν : ν ∈ minimalWeights P w) (j : J) :
    P.reflection j ν ∈ minimalWeights P w := by
  refine ⟨?_, by rw [rootForm_reflection_reflection_apply, hν.2]⟩
  rw [reflection_apply, sub_right_comm]
  exact sub_mem hν.1 (Submodule.smul_mem _ _ (root_mem_rootSpan j))

lemma eq_of_pairing_eq {w ν ν' : X} (hν : ν ∈ minimalWeights P w)
    (hν' : ν' ∈ minimalWeights P w)
    (h : ∀ j, P.toLinearMap ν (P.coroot j) = P.toLinearMap ν' (P.coroot j)) : ν = ν' := by
  have hd : ν - ν' ∈ P.rootSpan ℤ := by
    have := sub_mem hν.1 hν'.1
    rwa [sub_sub_sub_cancel_right] at this
  by_contra hne
  have hx : (⟨ν - ν', hd⟩ : P.rootSpan ℤ) ≠ 0 := by
    intro h0
    apply hne
    simpa [sub_eq_zero] using congrArg Subtype.val h0
  obtain ⟨i, hi⟩ := P.exists_coroot_ne ℤ hx
  apply hi
  apply FaithfulSMul.algebraMap_injective ℤ ℤ
  rw [algebraMap_coroot'In_apply]
  simp [h i]

lemma minimalWeights_finite (w : X) : (minimalWeights P w).Finite := by
  let f : X → J → ℤ := fun ν j ↦ P.toLinearMap ν (P.coroot j)
  refine Set.Finite.of_finite_image (f := f) ?_ ?_
  · refine (Set.Finite.pi (t := fun _ : J ↦ Icc (-1 : ℤ) 1) fun _ ↦ finite_Icc _ _).subset ?_
    rintro _ ⟨ν, hν, rfl⟩
    simp only [mem_pi, mem_univ, mem_Icc, forall_const, f]
    exact fun j ↦ ⟨neg_one_le_pairing hν j, pairing_le_one hν j⟩
  · intro ν hν ν' hν' h
    exact eq_of_pairing_eq hν hν' fun j ↦ congrFun h j

end Langlands.GroupScheme.SplitExistence
