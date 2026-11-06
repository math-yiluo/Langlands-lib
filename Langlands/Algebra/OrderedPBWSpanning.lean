import Langlands.Algebra.OrderedPBWWords
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

variable {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]
variable {n : ℕ} (b : Module.Basis (Fin n) k L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Evaluate a basis-index word in the actual universal enveloping algebra. -/
def basisWord (w : List (Fin n)) : UniversalEnvelopingAlgebra k L :=
  (w.map fun i => UniversalEnvelopingAlgebra.ι k (b i)).prod

@[simp]
theorem basisWord_nil : basisWord b [] = 1 := rfl

@[simp]
theorem basisWord_cons (i : Fin n) (w : List (Fin n)) :
    basisWord b (i :: w) = UniversalEnvelopingAlgebra.ι k (b i) * basisWord b w := rfl

@[simp]
theorem basisWord_append (a c : List (Fin n)) :
    basisWord b (a ++ c) = basisWord b a * basisWord b c := by
  simp [basisWord, List.map_append, List.prod_append]

theorem generator_eq_sum_basis (x : L) :
    UniversalEnvelopingAlgebra.ι k x =
      ∑ i : Fin n, b.repr x i • UniversalEnvelopingAlgebra.ι k (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul]

/-- The actual quotient relation, expanded in the supplied basis. -/
theorem basisWord_adjacent_swap (a : List (Fin n)) (i j : Fin n) (c : List (Fin n)) :
    basisWord b (a ++ i :: j :: c) = basisWord b (a ++ j :: i :: c) +
      ∑ l : Fin n, b.repr ⁅b i, b j⁆ l • basisWord b (a ++ l :: c) := by
  have hij : UniversalEnvelopingAlgebra.ι k (b i) * UniversalEnvelopingAlgebra.ι k (b j) =
      UniversalEnvelopingAlgebra.ι k (b j) * UniversalEnvelopingAlgebra.ι k (b i) +
        ∑ l : Fin n, b.repr ⁅b i, b j⁆ l • UniversalEnvelopingAlgebra.ι k (b l) := by
    have h := (UniversalEnvelopingAlgebra.ι k).map_lie (b i) (b j)
    change UniversalEnvelopingAlgebra.ι k ⁅b i, b j⁆ =
      UniversalEnvelopingAlgebra.ι k (b i) * UniversalEnvelopingAlgebra.ι k (b j) -
      UniversalEnvelopingAlgebra.ι k (b j) * UniversalEnvelopingAlgebra.ι k (b i) at h
    rw [← generator_eq_sum_basis b]
    exact eq_add_of_sub_eq' h.symm
  simp only [basisWord_append, basisWord_cons]
  simpa only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum, mul_smul_comm,
    smul_mul_assoc, mul_assoc] using
    congrArg (fun t => basisWord b a * (t * basisWord b c)) hij

/-- Every basis word is a linear combination of the actual ascending power products. -/
theorem basisWord_mem_ordered_span (w : List (Fin n)) :
    basisWord b w ∈ Submodule.span k (Set.range (orderedPBWMonomial b)) := by
  induction w using (List.Shortlex.wf (wellFounded_lt (α := Fin n))).induction with
  | h w ih =>
    by_cases hw : w.Pairwise (· ≤ ·)
    · have heval : basisWord b w = orderedPBWMonomial b (fun i => w.count i) := by
        conv_lhs => rw [pairwise_eq_exponentWord w hw]
        exact exponentWord_product b _
      rw [heval]
      exact Submodule.subset_span ⟨_, rfl⟩
    · obtain ⟨a, i, j, c, rfl, hji⟩ := exists_adjacent_inversion w hw
      rw [basisWord_adjacent_swap]
      apply Submodule.add_mem
      · exact ih _ (shortlex_adjacent_swap a i j c hji)
      · apply Submodule.sum_mem
        intro l _
        apply Submodule.smul_mem
        apply ih
        apply List.Shortlex.of_length_lt
        simp only [List.length_append, List.length_cons]
        omega

/-- The word span is closed under multiplication, by concatenation of basis words. -/
theorem basisWord_span_mul {a c : UniversalEnvelopingAlgebra k L}
    (ha : a ∈ Submodule.span k (Set.range (basisWord b)))
    (hc : c ∈ Submodule.span k (Set.range (basisWord b))) :
    a * c ∈ Submodule.span k (Set.range (basisWord b)) := by
  refine Submodule.span_induction₂
    (p := fun a c _ _ => a * c ∈ Submodule.span k (Set.range (basisWord b)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hc
  · intro a c ha hc
    obtain ⟨w, rfl⟩ := ha
    obtain ⟨z, rfl⟩ := hc
    rw [← basisWord_append]
    exact Submodule.subset_span ⟨_, rfl⟩
  · intro c _
    simpa only [zero_mul] using (Submodule.span k (Set.range (basisWord b))).zero_mem
  · intro a _
    simpa only [mul_zero] using (Submodule.span k (Set.range (basisWord b))).zero_mem
  · intro a a' c _ _ _ ha ha'
    simpa only [add_mul] using (Submodule.span k (Set.range (basisWord b))).add_mem ha ha'
  · intro a c c' _ _ _ hc hc'
    simpa only [mul_add] using (Submodule.span k (Set.range (basisWord b))).add_mem hc hc'
  · intro r a c _ _ hac
    simpa only [smul_mul_assoc] using
      (Submodule.span k (Set.range (basisWord b))).smul_mem r hac
  · intro r a c _ _ hac
    simpa only [mul_smul_comm] using
      (Submodule.span k (Set.range (basisWord b))).smul_mem r hac

/-- Basis words span the actual quotient, using tensor-algebra induction. -/
theorem span_basisWord_eq_top :
    Submodule.span k (Set.range (basisWord b)) = ⊤ := by
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (UniversalEnvelopingAlgebra.ringCon k L) a
  change UniversalEnvelopingAlgebra.mkAlgHom k L t ∈ _
  have hunit : (1 : UniversalEnvelopingAlgebra k L) ∈
      Submodule.span k (Set.range (basisWord b)) :=
    Submodule.subset_span ⟨[], rfl⟩
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    simpa only [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul, map_one] using
      (Submodule.span k (Set.range (basisWord b))).smul_mem r hunit
  | ι x =>
    change UniversalEnvelopingAlgebra.ι k x ∈ _
    rw [generator_eq_sum_basis b]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨[i], by simp⟩
  | mul x y hx hy =>
    rw [map_mul]
    exact basisWord_span_mul b hx hy
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- The full spanning clause of finite-basis PBW, with no independence premise. -/
theorem orderedPBWMonomial_span :
    Submodule.span k (Set.range (orderedPBWMonomial b)) = ⊤ := by
  rw [← span_basisWord_eq_top b]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    rw [← exponentWord_product b e]
    exact Submodule.subset_span ⟨exponentWord e, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact basisWord_mem_ordered_span b w

end Langlands.Algebra.UniversalEnveloping
