import Langlands.Group.RelativeWeylAssociatedSubsetProof
import Langlands.Group.RelativeWeylLongestProof

/-!
# Involutive reindexing by the associated subset

The longest representative for the associated subset is the inverse of the
original representative. Thus the associated-subset operation is an involution,
and gives a cardinality-preserving permutation of all simple-root subsets.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical
noncomputable section

private theorem length_le_longest_product [Fintype W] {J : Finset B} {b : W}
    (hb : b ∈ standardSubgroup cs J)
    (hbmax : ∀ y ∈ standardSubgroup cs J, cs.length y ≤ cs.length b) (y : W) :
    cs.length y ≤ cs.length (b * longestRep cs J) := by
  let d := longestRep cs J
  have hdmin : IsMinimal cs J ∅ d :=
    (mem_minimalReps cs J ∅ d).mp (longestRep_mem cs J)
  have hdL : ∀ x ∈ standardSubgroup cs J, cs.length d ≤ cs.length (x * d) := by
    intro x hx
    simpa using hdmin x hx 1 (standardSubgroup cs ∅).one_mem
  have hbd := length_mul_of_left_minimal cs hdL hb
  obtain ⟨z, ⟨a, ha, c, hc, hz⟩, hzmin⟩ := exists_minimal_in_doubleCoset cs J ∅ y
  have hc1 : c = 1 := by simpa using hc
  subst c
  have hzL : ∀ x ∈ standardSubgroup cs J, cs.length z ≤ cs.length (x * z) := by
    intro x hx
    simpa using hzmin x hx 1 (standardSubgroup cs ∅).one_mem
  have hy : y = a⁻¹ * z := by rw [hz]; group
  have hly : cs.length y = cs.length a⁻¹ + cs.length z := by
    rw [hy]
    exact length_mul_of_left_minimal cs hzL ((standardSubgroup cs J).inv_mem ha)
  have h1 := hbmax _ ((standardSubgroup cs J).inv_mem ha)
  have h2 : cs.length z ≤ cs.length d :=
    length_le_longestRep cs J ((mem_minimalReps cs J ∅ _).mpr hzmin)
  change cs.length y ≤ cs.length (b * d)
  omega

/-- Inversion interchanges the longest representatives for associated subsets. -/
theorem longestRep_associatedSubset [Fintype B] [Fintype W] (J : Finset B) :
    longestRep cs (associatedSubset cs J) = (longestRep cs J)⁻¹ := by
  let d := longestRep cs J
  let K := associatedSubset cs J
  have hconj : standardSubgroup cs K =
      (standardSubgroup cs J).map (MulAut.conj d⁻¹).toMonoidHom :=
    (associatedSubsetLaws_proof cs J).2.2
  have hdmin : IsMinimal cs J ∅ d :=
    (mem_minimalReps cs J ∅ d).mp (longestRep_mem cs J)
  have hdL : ∀ x ∈ standardSubgroup cs J, cs.length d ≤ cs.length (x * d) := by
    intro x hx
    simpa using hdmin x hx 1 (standardSubgroup cs ∅).one_mem
  have hdinv : IsMinimal cs K ∅ d⁻¹ := by
    intro x hx c hc
    have hc1 : c = 1 := by simpa using hc
    subst c
    rw [hconj] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have h := hdL a⁻¹ ((standardSubgroup cs J).inv_mem ha)
    have he : cs.length (d⁻¹ * a) = cs.length (a⁻¹ * d) := by
      rw [← cs.length_inv (d⁻¹ * a)]
      simp
    change cs.length d⁻¹ ≤ cs.length ((d⁻¹ * a * d⁻¹⁻¹) * d⁻¹ * 1)
    simpa only [inv_inv, mul_assoc, mul_inv_cancel, mul_one, cs.length_inv, he] using h
  have hdinvL : ∀ x ∈ standardSubgroup cs K,
      cs.length d⁻¹ ≤ cs.length (x * d⁻¹) := by
    intro x hx
    simpa using hdinv x hx 1 (standardSubgroup cs ∅).one_mem
  obtain ⟨b, hbmem, hbmax⟩ := (Finset.univ.filter
    (fun y => y ∈ standardSubgroup cs J)).exists_max_image cs.length ⟨1, by simp⟩
  have hb : b ∈ standardSubgroup cs J := by simpa using hbmem
  have hbmax' : ∀ y ∈ standardSubgroup cs J, cs.length y ≤ cs.length b :=
    fun y hy => hbmax y (by simpa using hy)
  let b' := d⁻¹ * b * d
  have hb' : b' ∈ standardSubgroup cs K := by
    rw [hconj]
    exact ⟨b, hb, by simp [b']⟩
  have hlenb' : cs.length b' = cs.length b := by
    have h1 := length_mul_of_left_minimal cs hdinvL hb'
    have h2 := length_mul_of_left_minimal cs hdL ((standardSubgroup cs J).inv_mem hb)
    have he : cs.length (b' * d⁻¹) = cs.length (b⁻¹ * d) := by
      rw [← cs.length_inv (b' * d⁻¹)]
      simp [b', mul_assoc]
    rw [he, cs.length_inv] at h1
    rw [cs.length_inv] at h2
    omega
  symm
  apply longestRepresentativeUnique_proof cs K d⁻¹
    ((mem_minimalReps cs K ∅ _).mpr hdinv)
  intro x hx
  have hxL : ∀ a ∈ standardSubgroup cs K, cs.length x ≤ cs.length (a * x) := by
    intro a ha
    simpa using (mem_minimalReps cs K ∅ x).mp hx a ha 1
      (standardSubgroup cs ∅).one_mem
  have h1 := length_mul_of_left_minimal cs hxL hb'
  have h2 := length_le_longest_product cs hb hbmax' (b' * x)
  have h3 := length_mul_of_left_minimal cs hdL hb
  rw [hlenb'] at h1
  rw [cs.length_inv]
  change cs.length (b' * x) ≤ cs.length (b * d) at h2
  omega

/-- Applying the associated-subset operation twice returns the original subset. -/
theorem associatedSubset_involutive [Fintype B] [Fintype W] :
    Function.Involutive (associatedSubset cs) := by
  intro J
  classical
  change simpleImage cs (longestRep cs (associatedSubset cs J))⁻¹
    (associatedSubset cs J) = J
  rw [longestRep_associatedSubset, inv_inv]
  ext j
  simp only [associatedSubset, simpleImage, Finset.mem_filter, Finset.mem_univ,
    true_and, inv_inv]
  constructor
  · rintro ⟨k, ⟨i, hi, hik⟩, hkj⟩
    have hij : cs.simple i = cs.simple j := by
      rw [← hkj, ← hik]
      group
    exact simple_injective cs hij ▸ hi
  · intro hj
    obtain ⟨k, -, hk⟩ := (associatedSubsetLaws_proof cs J).1 j hj
    simp only [inv_inv] at hk
    refine ⟨k, ⟨j, hj, hk⟩, ?_⟩
    rw [← hk]
    group

/-- Aubert's associated-subset reindexing as an equivalence of all subsets. -/
def associatedSubsetEquiv [Fintype B] [Fintype W] : Finset B ≃ Finset B :=
  (associatedSubset_involutive cs).toPerm

@[simp]
theorem associatedSubsetEquiv_apply [Fintype B] [Fintype W] (J : Finset B) :
    associatedSubsetEquiv cs J = associatedSubset cs J := rfl

@[simp]
theorem card_associatedSubsetEquiv [Fintype B] [Fintype W] (J : Finset B) :
    (associatedSubsetEquiv cs J).card = J.card :=
  (associatedSubsetLaws_proof cs J).2.1

end

end Langlands.Group.RelativeWeylIndexing
