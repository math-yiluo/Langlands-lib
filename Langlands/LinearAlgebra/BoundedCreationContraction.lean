import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Fintype.Card

/-! # Generation in a bounded family with creation and contraction maps -/

noncomputable section

universe u v w

namespace Langlands.LinearAlgebra.BoundedCreationContraction

variable {R : Type u} [CommRing R] {ι : Type v}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

/-- The submodules generated from the entire degree-one module by the creation
maps. Degree zero is included only to simplify the contraction induction. -/
def creationSpan (c : ∀ (_ : ι) (n : ℕ), M n →ₗ[R] M (n + 1)) :
    ∀ n, Submodule R (M n)
  | 0 => ⊤
  | 1 => ⊤
  | n + 2 => ⨆ i, (creationSpan c (n + 1)).map (c i (n + 1))

lemma creationSpan_raise
    (c : ∀ (_ : ι) (n : ℕ), M n →ₗ[R] M (n + 1))
    (i : ι) (n : ℕ) {x : M n} (hx : x ∈ creationSpan c n) :
    c i n x ∈ creationSpan c (n + 1) := by
  cases n with
  | zero => trivial
  | succ n =>
    exact (le_iSup (fun j => (creationSpan c (n + 1)).map (c j (n + 1))) i)
      (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

section Relations

variable [DecidableEq ι]
  (c : ∀ (_ : ι) (n : ℕ), M n →ₗ[R] M (n + 1))
  (d : ∀ (_ : ι) (n : ℕ), M (n + 1) →ₗ[R] M n)
  (hrel : ∀ i j n,
    (d i (n + 1)).comp (c j (n + 1)) + (c j n).comp (d i n) =
      if i = j then LinearMap.id else 0)

include hrel

lemma creationSpan_lower (i : ι) (n : ℕ) :
    ∀ x ∈ creationSpan c (n + 1), d i n x ∈ creationSpan c n := by
  induction n with
  | zero => intro x hx; trivial
  | succ n ih =>
    change creationSpan c (n + 2) ≤ (creationSpan c (n + 1)).comap (d i (n + 1))
    rw [creationSpan]
    refine iSup_le fun j => ?_
    rintro _ ⟨x, hx, rfl⟩
    change d i (n + 1) (c j (n + 1) x) ∈ creationSpan c (n + 1)
    have hcd := creationSpan_raise c j n (ih x hx)
    have heq := LinearMap.congr_fun (hrel i j n) x
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at heq
    by_cases hij : i = j
    · rw [ite_eq_left hij, LinearMap.id_apply] at heq
      rw [eq_sub_iff_add_eq.mpr heq]
      exact Submodule.sub_mem _ hx hcd
    · rw [ite_eq_right hij, LinearMap.zero_apply] at heq
      rw [eq_neg_iff_add_eq_zero.mpr heq]
      exact Submodule.neg_mem _ hcd

/-- If each remaining contraction of `x` belongs to a stable submodule, enough
distinct creation directions force `x` into that submodule by boundedness. -/
lemma mem_of_contractions_mem [Fintype ι]
    (W : ∀ n, Submodule R (M n))
    (hraise : ∀ i n x, x ∈ W n → c i n x ∈ W (n + 1))
    (hlower : ∀ i n x, x ∈ W (n + 1) → d i n x ∈ W n)
    (hbound : ∀ n, Fintype.card ι < n → Subsingleton (M n))
    (s : Finset ι) :
    ∀ n (x : M (n + 1)),
      (∀ i ∈ s, d i n x ∈ W n) →
      Fintype.card ι < n + 1 + s.card → x ∈ W (n + 1) := by
  induction s using Finset.induction_on with
  | empty =>
    intro n x hd hn
    have : Subsingleton (M (n + 1)) := hbound _ (by simpa using hn)
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  | @insert i s hi ih =>
    intro n x hd hn
    have hds : ∀ j ∈ s, d j (n + 1) (c i (n + 1) x) ∈ W (n + 1) := by
      intro j hj
      have hji : j ≠ i := by
        intro h
        exact hi (h ▸ hj)
      have heq := LinearMap.congr_fun (hrel j i n) x
      simp only [LinearMap.add_apply, LinearMap.comp_apply,
        ite_eq_right hji, LinearMap.zero_apply] at heq
      rw [eq_neg_iff_add_eq_zero.mpr heq]
      exact Submodule.neg_mem _ (hraise i n _ (hd j (Finset.mem_insert_of_mem hj)))
    have hy : c i (n + 1) x ∈ W (n + 2) :=
      ih (n + 1) (c i (n + 1) x) hds (by
        rw [Finset.card_insert_of_notMem hi] at hn
        omega)
    have heq : d i (n + 1) (c i (n + 1) x) + c i n (d i n x) = x := by
      simpa using LinearMap.congr_fun (hrel i i n) x
    rw [← heq]
    exact Submodule.add_mem _ (hlower i (n + 1) _ hy)
      (hraise i n _ (hd i (Finset.mem_insert_self _ _)))

/-- A bounded family with `card ι` creation directions and the creation-contraction
relations is generated from its degree-one module in every positive degree. -/
theorem creationSpan_eq_top [Fintype ι]
    (hbound : ∀ n, Fintype.card ι < n → Subsingleton (M n)) (n : ℕ) :
    creationSpan c (n + 1) = ⊤ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply top_unique
    intro x hx
    apply mem_of_contractions_mem c d hrel (creationSpan c)
      (fun i n x hx => creationSpan_raise c i n hx)
      (fun i n x hx => creationSpan_lower c d hrel i n x hx)
      hbound Finset.univ (n + 1) x
    · intro i hi
      rw [ih]
      trivial
    · simp only [Finset.card_univ]
      omega

/-- In particular, the degree-two module is spanned by the images of the
degree-one creation maps. No characteristic or division hypothesis is needed. -/
theorem iSup_range_degreeOne_eq_top [Fintype ι]
    (hbound : ∀ n, Fintype.card ι < n → Subsingleton (M n)) :
    (⨆ i, LinearMap.range (c i 1)) = ⊤ := by
  simpa only [creationSpan, Submodule.map_top] using
    creationSpan_eq_top c d hrel hbound 1

end Relations

end Langlands.LinearAlgebra.BoundedCreationContraction
