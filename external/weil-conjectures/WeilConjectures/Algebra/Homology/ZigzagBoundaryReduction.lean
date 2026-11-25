/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Algebra.Homology.ZigzagModuleFunctorial
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.Algebra.Homology.ZigzagToRowCokernel

/-! # Removing the zeroth component of a row boundary

Source: Stacks Project, Algebra, Tag 00M1 (`lemma-no-spectral-sequence`),
injectivity argument. (blueprint: new-zigzag-boundary-reduction).
-/

@[expose] public section

open CategoryTheory
namespace HomologicalComplex₂
universe u v
variable {R : Type u} [CommRing R]
/-- The row-cokernel boundary hypothesis permits subtracting one trivial zig-zag
 to kill the `(0,n)` component.

Source: Stacks Project, Algebra, Tag 00M1 (`lemma-no-spectral-sequence`),
injectivity argument, lines 18488--18496.
(blueprint: new-zigzag-boundary-reduction).

Let `π = A.pOpcycles 0`. Lift the witness `y` of `hboundary` through the
surjective cokernel projection `π` in degree `n+1`, obtaining `c` in `A₀,ₙ₊₁`.
The chain-map identity for `π` gives `πₙ(a₀,ₙ - δ c) = 0`. The kernel of this
cokernel projection is the image of `d : A₁,ₙ → A₀,ₙ`, so choose `e` with
`d e = a₀,ₙ - δ c`. Define `b` to be the sum of the direct-sum inclusions of
`c` at `(0,n+1)` and `e` at `(1,n)`. Its boundary has zeroth component
`δ c + d e = a₀,ₙ`. Boundaries are cycles by the first clause of
`zigzagModule_functorial`; hence `a - zigzagBoundary A n b` is a cycle by
submodule closure under subtraction, and its zeroth component is zero by
linearity of the component projection. The construction also works for `n=0`;
row exactness is not used in this initial reduction. -/
theorem zigzagBoundary_reduction
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ) (a : zigzagTotal A n) (ha : a ∈ zigzagCycles A n)
    (hboundary : ∃ y : (A.opcycles 0).X (n + 1),
      (A.opcycles 0).d (n + 1) n y = (A.pOpcycles 0).f n
        (DirectSum.component R (ZigzagIndex n)
          (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩ a)) :
    ∃ b : zigzagTotal A (n + 1),
      a - zigzagBoundary A n b ∈ zigzagCycles A n ∧
      DirectSum.component R (ZigzagIndex n)
        (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
        ⟨(0, n), by simp⟩ (a - zigzagBoundary A n b) = 0 := by
  classical
  have _ := hrow
  let endpoint := DirectSum.component R (ZigzagIndex n)
    (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩
  obtain ⟨_, hprojection, _⟩ := exists_zigzagToRowCokernel (R := R) n
  obtain ⟨y, hy⟩ := hboundary
  obtain ⟨c, hc⟩ := (hprojection A (n + 1)).1 y
  have hcomm := ConcreteCategory.congr_hom ((A.pOpcycles 0).comm (n + 1) n) c
  dsimp at hcomm
  have hker : endpoint a - ((A.X 0).d (n + 1) n) c ∈
      LinearMap.ker ((A.pOpcycles 0).f n).hom := by
    change ((A.pOpcycles 0).f n)
      (endpoint a - ((A.X 0).d (n + 1) n) c) = 0
    rw [map_sub, ← hcomm, hc, hy]
    exact sub_self _
  rw [(hprojection A n).2] at hker
  obtain ⟨e, he⟩ := hker
  let b : zigzagTotal A (n + 1) :=
    DirectSum.lof R (ZigzagIndex (n + 1))
      (fun i : ZigzagIndex (n + 1) => (A.X i.1.1).X i.1.2)
      ⟨(0, n + 1), by simp⟩ c +
    DirectSum.lof R (ZigzagIndex (n + 1))
      (fun i : ZigzagIndex (n + 1) => (A.X i.1.1).X i.1.2)
      ⟨(1, n), by omega⟩ e
  have hbc : endpoint (zigzagBoundary A n b) =
      ((A.X 0).d (n + 1) n) c + ((A.d 1 0).f n) e := by
    cases n <;>
      simp only [b, endpoint, zigzagBoundary, map_add, DirectSum.toModule_lof,
        zigzagBoundaryComponent, Nat.reduceAdd, lt_self_iff_false, ↓reduceDIte,
        lt_add_iff_pos_left, add_pos_iff, Order.lt_two_iff, zero_le, or_true,
        Nat.add_one_sub_one, zero_add, LinearMap.coe_comp, Function.comp_apply,
        Order.lt_one_iff, Order.lt_add_one_iff, LinearMap.add_apply, add_zero,
        DirectSum.component.lof_self, DirectSum.component.of, add_right_inj,
        add_eq_left, dite_eq_right_iff]
    all_goals
      intro h
      have hfirst := congrArg (fun i : ZigzagIndex _ ↦ i.val.1) h
      simp at hfirst
  refine ⟨b, (zigzagCycles A n).sub_mem ha ?_, ?_⟩
  · apply (zigzagModule_functorial A A A (𝟙 A) (𝟙 A) n).1
    exact ⟨b, rfl⟩
  · change endpoint (a - zigzagBoundary A n b) = 0
    rw [map_sub, hbc, he]
    abel


end HomologicalComplex₂
