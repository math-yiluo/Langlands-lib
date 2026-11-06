import Langlands.Algebra.TriangularWordNormalization
import Langlands.Algebra.OrderedPBWWords

noncomputable section

universe u v
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping.PBW

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
variable {n : ℕ}

abbrev WordModule (k : Type u) [Zero k] (n : ℕ) := List (Fin n) →₀ k

/-- Prepend a basis index to every word. -/
def prepend (i : Fin n) : WordModule k n →ₗ[k] WordModule k n :=
  Finsupp.lmapDomain k k (List.cons i)

@[simp]
theorem prepend_single (i : Fin n) (w : List (Fin n)) (a : k) :
    prepend i (Finsupp.single w a) = Finsupp.single (i :: w) a :=
  Finsupp.mapDomain_single

/-- Insert a Lie algebra element on the left by its basis coordinates. -/
def insert (b : Module.Basis (Fin n) k L) : L →ₗ[k] Module.End k (WordModule k n) :=
  b.constr k prepend

@[simp]
theorem insert_basis (b : Module.Basis (Fin n) k L) (i : Fin n) :
    insert b (b i) = prepend i := by
  simp [insert]

theorem insert_apply (b : Module.Basis (Fin n) k L) (x : L) (p : WordModule k n) :
    insert b x p = ∑ i, (b.repr x i) • prepend i p := by
  simp [insert, Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply,
    LinearMap.sum_apply]

/-- A single adjacent inversion may be reduced at any position in a word. -/
inductive Reduction (b : Module.Basis (Fin n) k L) :
    List (Fin n) → WordModule k n → Prop
  | head (i j : Fin n) (w : List (Fin n)) (h : j < i) :
      Reduction b (i :: j :: w)
        (Finsupp.single (j :: i :: w) 1 +
          insert b ⁅b i, b j⁆ (Finsupp.single w 1))
  | cons (i : Fin n) {w : List (Fin n)} {p : WordModule k n} :
      Reduction b w p → Reduction b (i :: w) (prepend i p)

abbrev WordLT : List (Fin n) → List (Fin n) → Prop := List.Shortlex (· < ·)

theorem wordLT_wf : WellFounded (WordLT (n := n)) :=
  List.Shortlex.wf wellFounded_lt

theorem mem_support_prepend {i : Fin n} {p : WordModule k n} {s : List (Fin n)}
    (hs : s ∈ (prepend i p).support) :
    ∃ t ∈ p.support, s = i :: t := by
  classical
  let e : List (Fin n) ↪ List (Fin n) := ⟨List.cons i, List.cons_injective⟩
  change s ∈ (Finsupp.mapDomain e p).support at hs
  rw [Finsupp.support_mapDomain_embedding] at hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
  exact ⟨t, ht, rfl⟩

theorem insert_single_supported (b : Module.Basis (Fin n) k L) (x : L)
    (w : List (Fin n)) :
    insert b x (Finsupp.single w 1) ∈
      Finsupp.supported k k {s | s.length = w.length + 1} := by
  classical
  rw [insert_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  rw [prepend_single]
  exact Finsupp.single_mem_supported k 1 (by simp)

theorem reduction_triangular (b : Module.Basis (Fin n) k L) :
    TriangularNormalization.Triangular WordLT (Reduction b) := by
  classical
  intro w p hp
  induction hp with
  | head i j w hij =>
    intro s hs
    rcases Finset.mem_union.mp (Finsupp.support_add hs) with hs | hs
    · have heq : s = j :: i :: w := ((Finsupp.mem_support_single _ _ _).mp hs).1
      subst s
      exact shortlex_adjacent_swap [] i j w hij
    · apply List.Shortlex.of_length_lt
      have hlen := insert_single_supported b ⁅b i, b j⁆ w hs
      simp only [Set.mem_ofPred_eq] at hlen
      simp only [List.length_cons]
      omega
  | cons i hp ih =>
    intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_support_prepend hs
    exact List.Shortlex.cons (ih t ht)

theorem reduction_not_pairwise (b : Module.Basis (Fin n) k L)
    {w : List (Fin n)} {p : WordModule k n} (hp : Reduction b w p) :
    ¬ w.Pairwise (· ≤ ·) := by
  induction hp with
  | head i j w hij =>
    intro hw
    exact (not_le_of_gt hij) ((List.pairwise_cons.mp hw).1 j (by simp))
  | cons i hp ih =>
    exact fun hw => ih (List.pairwise_cons.mp hw).2

theorem reduction_context (b : Module.Basis (Fin n) k L) (a : List (Fin n))
    (i j : Fin n) (w : List (Fin n)) (hij : j < i) :
    ∃ p, Reduction b (a ++ i :: j :: w) p := by
  induction a with
  | nil => exact ⟨_, Reduction.head i j w hij⟩
  | cons t a ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨_, Reduction.cons t hp⟩

theorem irreducible_iff_pairwise (b : Module.Basis (Fin n) k L)
    (w : List (Fin n)) :
    TriangularNormalization.Irreducible (Reduction b) w ↔ w.Pairwise (· ≤ ·) := by
  constructor
  · intro hw
    by_contra h
    obtain ⟨a, i, j, t, rfl, hij⟩ := exists_adjacent_inversion w h
    exact hw (reduction_context b a i j t hij)
  · intro hw ⟨p, hp⟩
    exact reduction_not_pairwise b hp hw

end Langlands.Algebra.UniversalEnveloping.PBW
