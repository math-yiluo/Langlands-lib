/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Bounded complexes belong to triangulated subcategories containing their terms

Source: literature/stacks-project/derived.tex, Tag 0FCP, lemma-K-bounded-derived
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/--
A bounded complex belongs to a strictly full triangulated subcategory containing each
of its terms in degree zero.

Source: literature/stacks-project/derived.tex, Tag 0FCP, lemma-K-bounded-derived, proof:
the displayed stupid-truncation triangles and finite induction
(auxiliary; not a blueprint node).

Proof:
1. If `a > b`, the support condition makes every term zero. The complex is isomorphic
   to zero, as is its image under `Q`, so it belongs to `S`. Otherwise let `T n` be the
   stupid tail with terms `K.X q` for `n ≤ q` and zero below. The support bounds identify
   `T a` with `K` and `T (b + 1)` with zero (def-weil-abstract-derived-category).
2. For `a ≤ n ≤ b`, let `E n` be `K.X n` placed in degree `n`. The termwise inclusion
   `T (n + 1) → T n` and projection `T n → E n` commute with differentials. In degree
   `n` their sequence is `0 → K.X n → K.X n`, in higher degrees it is the identity
   followed by zero, and below `n` it is zero. Thus it is degreewise short exact
   (def-sp-abelian).
3. By lem-weil-pbc-complex-ses-triangle this sequence gives a distinguished triangle
   `Q(T (n + 1)) → Q(T n) → Q(E n) → Q(T (n + 1))[1]`.
4. The shift convention gives `E n ≅ (K.X n)[0][-n]`. As `Q` commutes with shifts,
   the term hypothesis and shift/isomorphism closure put `Q(E n)` in `S`
   (def-weil-abstract-derived-category).
5. For `N = b - a + 1`, induct on `k = 0,...,N` to put `Q(T (b + 1 - k))` in `S`.
   The base case is zero. At each step put `n = b - k` and rotate the triangle twice:
   its vertices are `Q(E n)`, `Q(T (n + 1))[1]`, `Q(T n)[1]`. The first two belong
   to `S`; third-vertex closure and shifting back give `Q(T n)` in `S`
   (def-weil-triangulated-category). The endpoint and `T a ≅ K` give the result.
-/
theorem bounded_complex_mem_triangulated
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ObjectProperty (DerivedCategory C)) [S.IsTriangulated]
    [S.IsClosedUnderIsomorphisms] (K : CochainComplex C ℤ) (a b : ℤ)
    (hK : ∀ q : ℤ, q < a ∨ b < q → IsZero (K.X q))
    (hS : ∀ q : ℤ, a ≤ q → q ≤ b →
      S ((DerivedCategory.singleFunctor C 0).obj (K.X q))) :
    S (DerivedCategory.Q.obj K) := by
  -- Induct on an upper bound for the number of possible nonzero terms.
  suffices ∀ (n : ℕ) (L : CochainComplex C ℤ) (c : ℤ), b + 1 - c ≤ n →
      (∀ q : ℤ, q < c ∨ b < q → IsZero (L.X q)) →
      (∀ q : ℤ, c ≤ q → q ≤ b →
        S ((DerivedCategory.singleFunctor C 0).obj (L.X q))) →
      S (DerivedCategory.Q.obj L) by
    exact this (b + 1 - a).toNat K a (by omega) hK hS
  intro n
  induction n with
  | zero =>
    intro L c hc hL _
    apply S.prop_of_isZero
    apply DerivedCategory.Q.map_isZero
    rw [IsZero.iff_id_eq_zero]
    ext q
    exact (hL q (by omega)).eq_of_src _ _
  | succ n ih =>
    intro L c hc hL hterms
    by_cases hcb : c ≤ b
    · -- Project onto the lowest term; its kernel is the next stupid tail.
      let p : L ⟶ (HomologicalComplex.single C (.up ℤ) c).obj (L.X c) :=
        HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi ↦ by
          exact (hL i (Or.inl (by
            change i + 1 = c at hi
            omega))).eq_of_src _ _)
      have hp : IsIso (p.f c) := by
        dsimp [p]
        simp only [HomologicalComplex.mkHomToSingle_f, Category.id_comp]
        infer_instance
      have : Epi p := HomologicalComplex.epi_of_epi_f p (fun q ↦ by
        by_cases hq : q = c
        · subst hq
          infer_instance
        · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) c (L.X c) q hq).epi _)
      let E := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
      have hE : E.ShortExact := { exact := ShortComplex.exact_kernel p }
      have heval (q : ℤ) := hE.map (HomologicalComplex.eval C (.up ℤ) q)
      have hk (q : ℤ) (hq : q ≠ c) : IsIso ((kernel.ι p).f q) := by
        exact (heval q).isIso_f_iff.mpr
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) c (L.X c) q hq)
      have hzero : IsZero ((kernel p).X c) := by
        exact (heval c).isIso_g_iff.mp hp
      -- The kernel has one fewer possible nonzero term and the same higher terms.
      have htail : S (DerivedCategory.Q.obj (kernel p)) := by
        apply ih (kernel p) (c + 1) (by omega)
        · intro q hq
          by_cases hqc : q = c
          · subst hqc
            exact hzero
          · have := hk q hqc
            exact (hL q (by omega)).of_iso (asIso ((kernel.ι p).f q))
        · intro q hq hqb
          have := hk q (by omega)
          exact S.prop_of_iso
            ((DerivedCategory.singleFunctor C 0).mapIso
              (asIso ((kernel.ι p).f q))).symm (hterms q (by omega) hqb)
      have hsingle : S ((DerivedCategory.singleFunctor C c).obj (L.X c)) := by
        exact S.prop_of_iso (((DerivedCategory.singleFunctors C).shiftIso (-c) c 0
          (by omega)).app (L.X c)) (S.le_shift (-c) _ (hterms c le_rfl hcb))
      exact S.ext_of_isTriangulatedClosed₂ _
        (DerivedCategory.triangleOfSES_distinguished hE) htail hsingle
    · apply S.prop_of_isZero
      apply DerivedCategory.Q.map_isZero
      rw [IsZero.iff_id_eq_zero]
      ext q
      exact (hL q (by omega)).eq_of_src _ _

end CategoryTheory
