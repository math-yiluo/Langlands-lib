/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Algebra.Homology.ZigzagModuleFunctorial
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Exact-row induction for a zero-component zig-zag

Source: Stacks Project, Algebra, Tag 00M1 (`lemma-no-spectral-sequence`),
injectivity argument. (blueprint: new-zigzag-zero-component-boundary).
-/

@[expose] public section

open CategoryTheory
namespace HomologicalComplex₂
universe u v
variable {R : Type u} [CommRing R]
open Classical in
private lemma boundary_single_component
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n k q : ℕ) (h : k + q = n)
    (f : (A.X (k + 1)).X q) :
    DirectSum.component R (ZigzagIndex n)
      (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(k, q), h⟩
      (zigzagBoundary A n (DirectSum.lof R (ZigzagIndex (n + 1))
        (fun i : ZigzagIndex (n + 1) => (A.X i.1.1).X i.1.2)
        ⟨(k + 1, q), by omega⟩ f)) = ((A.d (k + 1) k).f q) f := by
  classical
  simp only [zigzagBoundary, DirectSum.toModule_lof, zigzagBoundaryComponent,
    Nat.zero_lt_succ, ↓reduceDIte, LinearMap.add_apply,
    LinearMap.comp_apply, map_add]
  split_ifs with hq
  · have hne : (⟨(k + 1, q - 1), by omega⟩ : ZigzagIndex n) ≠ ⟨(k, q), h⟩ := by
      intro he
      have := congrArg (fun i : ZigzagIndex n => i.1.1) he
      simp only at this
      omega
    simp [DirectSum.component.of, hne]
  · simp

open Classical in
private lemma boundary_single_lower
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n k q : ℕ) (h : k + q = n)
    (f : (A.X (k + 1)).X q) (j : ZigzagIndex n) (hj : j.1.1 < k) :
    DirectSum.component R (ZigzagIndex n)
      (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) j
      (zigzagBoundary A n (DirectSum.lof R (ZigzagIndex (n + 1))
        (fun i : ZigzagIndex (n + 1) => (A.X i.1.1).X i.1.2)
        ⟨(k + 1, q), by omega⟩ f)) = 0 := by
  classical
  have hne : (⟨(k, q), h⟩ : ZigzagIndex n) ≠ j := by
    intro he
    have := congrArg (fun i : ZigzagIndex n => i.1.1) he
    simp only at this
    omega
  simp only [zigzagBoundary, DirectSum.toModule_lof, zigzagBoundaryComponent,
    Nat.zero_lt_succ, ↓reduceDIte, LinearMap.add_apply,
    LinearMap.comp_apply, map_add]
  split_ifs with hq
  · have hne' : (⟨(k + 1, q - 1), by omega⟩ : ZigzagIndex n) ≠ j := by
      intro he
      have := congrArg (fun i : ZigzagIndex n => i.1.1) he
      simp only at this
      omega
    simp [DirectSum.component.of, hne, hne']
  · simp [DirectSum.component.of, hne]

/-- If a zig-zag has vanishing `(0,n)` component, successive exact-row lifts
 express it as a boundary.

Source: Stacks Project, Algebra, Tag 00M1 (`lemma-no-spectral-sequence`),
injectivity argument, lines 18496--18504.
(blueprint: new-zigzag-zero-component-boundary).

Maintain a residual cycle whose components of horizontal index below `k` are
zero, together with a tuple whose boundary is the difference from the original
cycle. Start at `k=1` with the original cycle and the zero tuple, using `hzero`.
For `1 ≤ k ≤ n`, its zig-zag equation at `(k-1,n-k)` says
`d aₖ,ₙ₋ₖ = δ aₖ₋₁,ₙ₋ₖ₊₁ = 0`. Row exactness at this positive index supplies
`f` in `Aₖ₊₁,ₙ₋ₖ` with `d f = aₖ,ₙ₋ₖ`. Subtract the boundary of the tuple
supported at `(k+1,n-k)` with value `f`. This kills the `k`-th component and
changes only the `(k+1,n-k-1)` component if `k<n`. Earlier components remain
zero. The first clause of `zigzagModule_functorial` and submodule subtraction
keep the residual a cycle. Add this tuple to the accumulated boundary preimage.
After `k=n`, all components are zero, so the original tuple is the boundary
of the accumulated tuple by linearity and direct-sum extensionality. For `n=0`,
the only index is `(0,0)`, so `hzero` already implies `a=0`, the boundary of zero.
No column exactness or assumptions on the ring's characteristic are used. -/
theorem zigzag_zero_component_boundary
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ) (a : zigzagTotal A n) (ha : a ∈ zigzagCycles A n)
    (hzero : DirectSum.component R (ZigzagIndex n)
      (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
      ⟨(0, n), by simp⟩ a = 0) :
    a ∈ zigzagBoundaries A n := by
  classical
  let c := fun j : ZigzagIndex n => DirectSum.component R (ZigzagIndex n)
    (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) j
  let D := zigzagBoundary A n
  have hbc : zigzagBoundaries A n ≤ zigzagCycles A n :=
    (zigzagModule_functorial A A A (𝟙 A) (𝟙 A) n).1
  -- The residual has zero components at every horizontal index below k.
  have eliminate : ∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
      ∃ b : zigzagTotal A (n + 1), ∀ j : ZigzagIndex n,
        j.1.1 < k → c j (a - D b) = 0 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _
      refine ⟨0, ?_⟩
      intro j hj
      have he : j = ⟨(0, n), by simp⟩ := by
        apply Subtype.ext
        apply Prod.ext <;> have := j.2 <;> dsimp at * <;> omega
      subst j
      simpa [c, D] using hzero
    | succ k hk ih =>
      intro hkn
      obtain ⟨b, hb⟩ := ih (by omega)
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      let q := n - (l + 1)
      have hkq : l + 1 + q = n := by dsimp [q]; omega
      let j : ZigzagIndex n := ⟨(l + 1, q), hkq⟩
      let r := a - D b
      have hr : r ∈ zigzagCycles A n :=
        (zigzagCycles A n).sub_mem ha (hbc ⟨b, rfl⟩)
      have hprev : c ⟨(l, q + 1), by omega⟩ r = 0 := hb _ (by simp)
      have hker : ((A.d (l + 1) l).f q) (c j r) = 0 := by
        have heq := hr l q (by omega)
        simp only [zigzagRelation, LinearMap.sub_apply, LinearMap.comp_apply] at heq
        simpa only [show DirectSum.component R (ZigzagIndex n)
            (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
            ⟨(l, q + 1), by omega⟩ r = 0 from hprev, map_zero, sub_zero]
          using heq
      obtain ⟨f, hf⟩ := (ShortComplex.moduleCat_exact_iff _).mp
        (hrow (l + 1) q (by omega)) (c j r) hker
      let t := DirectSum.lof R (ZigzagIndex (n + 1))
        (fun i : ZigzagIndex (n + 1) => (A.X i.1.1).X i.1.2)
        ⟨(l + 1 + 1, q), by omega⟩ f
      refine ⟨b + t, ?_⟩
      intro i hi
      have hres : a - D (b + t) = r - D t := by
        dsimp [r]
        rw [map_add, sub_add_eq_sub_sub]
      rw [hres, map_sub]
      by_cases hil : i.1.1 < l + 1
      · rw [hb i hil]
        have ht : c i (D t) = 0 := boundary_single_lower A n (l + 1) q hkq f i hil
        rw [ht, sub_self]
      · have he : i = j := by
          apply Subtype.ext
          apply Prod.ext <;> have := i.2 <;> dsimp [j] at * <;> omega
        subst i
        have ht : c j (D t) = ((A.d (l + 1 + 1) (l + 1)).f q) f :=
          boundary_single_component A n (l + 1) q hkq f
        rw [ht, hf, sub_self]
  -- At k = n + 1 every component of the residual vanishes, including for n = 0.
  obtain ⟨b, hb⟩ := eliminate (n + 1) (by omega) le_rfl
  have hz : a - D b = 0 := by
    apply DirectSum.ext_component R
    intro j
    rw [map_zero]
    exact hb j (by have := j.2; omega)
  exact ⟨b, (sub_eq_zero.mp hz).symm⟩

end HomologicalComplex₂
