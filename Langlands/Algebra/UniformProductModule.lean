import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Basic

/-! # Uniform finite generation for products of modules -/

namespace Langlands

/-- A product of modules, each over its own ring, has a spanning family indexed by `K`
if each factor has one. The product of rings acts coordinatewise. -/
theorem exists_spanningFamily_pi {I K : Type*} [Finite K]
    (R : I → Type*) (M : I → Type*) [∀ i, Semiring (R i)]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module (R i) (M i)]
    (h : ∀ i, ∃ g : K → M i, Submodule.span (R i) (Set.range g) = ⊤) :
    ∃ g : K → (∀ i, M i), Submodule.span (∀ i, R i) (Set.range g) = ⊤ := by
  classical
  let := Fintype.ofFinite K
  choose g hg using h
  refine ⟨fun k i => g i k, Submodule.eq_top_iff'.2 fun x => ?_⟩
  have hex (i : I) : ∃ c : K → R i, ∑ k, c k • g i k = x i := by
    apply (Submodule.mem_span_range_iff_exists_fun (R i)).mp
    simp [hg i]
  choose c hc using hex
  refine (Submodule.mem_span_range_iff_exists_fun (∀ i, R i)).mpr ⟨fun k i => c i k, ?_⟩
  funext i
  simpa only [Finset.sum_apply, Pi.smul_apply'] using hc i

/-- Let `p : J → I` label the ring acting on each factor `M j`. If the fibers of `p` embed
in a fixed finite type `L` and every `M j` is spanned by a `K`-indexed family, then the
product is spanned by an `(L × K)`-indexed family over the product of the rings. -/
def UniformProductSpanningStatement {I J : Type*} (K L : Type*) [Finite K] [Finite L]
    (R : I → Type*) (M : J → Type*) (p : J → I) [∀ i, Semiring (R i)]
    [∀ j, AddCommMonoid (M j)] [∀ j, Module (R (p j)) (M j)]
    [Module (∀ i, R i) (∀ j, M j)] : Prop :=
  (∀ (r : ∀ i, R i) (x : ∀ j, M j) (j : J), (r • x) j = r (p j) • x j) →
    (∀ i, Nonempty ({j // p j = i} ↪ L)) →
      (∀ j, ∃ g : K → M j, Submodule.span (R (p j)) (Set.range g) = ⊤) →
        ∃ g : L × K → (∀ j, M j), Submodule.span (∀ i, R i) (Set.range g) = ⊤

/-- Uniformly bounded fibers and spanning families give a common finite spanning
family for the product. -/
theorem exists_spanningFamily_pi_of_boundedFibers {I J K L : Type*} [Finite K] [Finite L]
    (R : I → Type*) (M : J → Type*) (p : J → I) [∀ i, Semiring (R i)]
    [∀ j, AddCommMonoid (M j)] [∀ j, Module (R (p j)) (M j)]
    [Module (∀ i, R i) (∀ j, M j)] :
    UniformProductSpanningStatement K L R M p := by
  intro hsmul hfib hgen
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite L
  let e (i : I) : {j // p j = i} ↪ L := (hfib i).some
  let label (j : J) : L := e (p j) ⟨j, rfl⟩
  choose g hg using hgen
  let generators (s : L × K) (j : J) : M j := if label j = s.1 then g j s.2 else 0
  refine ⟨generators, Submodule.eq_top_iff'.2 fun x => ?_⟩
  have hex (j : J) : ∃ c : K → R (p j), ∑ k, c k • g j k = x j := by
    apply (Submodule.mem_span_range_iff_exists_fun (R (p j))).mp
    simp [hg j]
  choose c hc using hex
  let coeff (s : L × K) (i : I) : R i :=
    if h : ∃ j : {j // p j = i}, e i j = s.1 then
      h.choose.property ▸ c h.choose s.2
    else 0
  have hcoeff (j : J) (k : K) : coeff (label j, k) (p j) = c j k := by
    have h : ∃ j' : {j' // p j' = p j}, e (p j) j' = label j := ⟨⟨j, rfl⟩, rfl⟩
    have hj : h.choose = ⟨j, rfl⟩ := (e (p j)).injective h.choose_spec
    simp only [coeff, dite_eq_left h]
    generalize h.choose = j' at hj ⊢
    subst j'
    rfl
  refine (Submodule.mem_span_range_iff_exists_fun (∀ i, R i)).mpr ⟨coeff, ?_⟩
  funext j
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_apply, hsmul]
  rw [Finset.sum_eq_single (label j)]
  · simpa only [generators, ite_eq_left rfl, hcoeff] using hc j
  · intro l _ hl
    simp [generators, Ne.symm hl]
  · simp

end Langlands
