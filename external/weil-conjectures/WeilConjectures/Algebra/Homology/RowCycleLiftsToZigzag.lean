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
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Row-cycle lifts to a zig-zag

Source: Stacks Project, Algebra, Lemma Tag 00M1, proof lines 18464--18481
(blueprint: lem-weil-pbc-double-complex-row-cycle-lifts-to-zigzag).
-/

@[expose] public section

open CategoryTheory DirectSum

namespace HomologicalComplex₂

variable {R : Type*} [CommRing R]

/-- The first adjacent equation follows from the degreewise cokernel sequence. -/
private theorem first_lift
    (A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (q : ℕ) (x : (A.X 0).X (q + 1))
    (hc : ∃ c : (A.opcycles 0).cycles (q + 1),
      (A.opcycles 0).iCycles (q + 1) c = (A.pOpcycles 0).f (q + 1) x) :
    ∃ y : (A.X 1).X q, (A.d 1 0).f q y = (A.X 0).d (q + 1) q x := by
  let S := ShortComplex.mk (A.d 1 0) (A.pOpcycles 0) (A.d_pOpcycles 1 0)
  have hS : S.Exact := S.exact_of_g_is_cokernel (A.opcyclesIsCokernel 1 0 (by simp))
  have he := (ShortComplex.moduleCat_exact_iff
    (S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) q))).mp
    (hS.map _) ((A.X 0).d (q + 1) q x)
  apply he
  obtain ⟨c, hc⟩ := hc
  change (A.pOpcycles 0).f q ((A.X 0).d (q + 1) q x) = 0
  have hh := congrArg (fun f => f x) ((A.pOpcycles 0).comm (q + 1) q)
  change (A.opcycles 0).d (q + 1) q ((A.pOpcycles 0).f (q + 1) x) =
    (A.pOpcycles 0).f q ((A.X 0).d (q + 1) q x) at hh
  rw [← hh, ← hc]
  exact congrArg (fun f => f c) ((A.opcycles 0).iCycles_d (q + 1) q)

/-- The next vertical image is a horizontal cycle, hence lifts by row exactness. -/
private theorem next_lift
    (A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p q : ℕ)
    (he : (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
      (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
        HomologicalComplex.zero_f])).Exact)
    (u : (A.X p).X (q + 1)) (v : (A.X (p - 1)).X (q + 2))
    (hu : (A.d p (p - 1)).f (q + 1) u = (A.X (p - 1)).d (q + 2) (q + 1) v) :
    ∃ y : (A.X (p + 1)).X q,
      (A.d (p + 1) p).f q y = (A.X p).d (q + 1) q u := by
  apply (ShortComplex.moduleCat_exact_iff _).mp he
  have hh := congrArg (fun f => f u) ((A.d p (p - 1)).comm (q + 1) q)
  change (A.X (p - 1)).d (q + 1) q ((A.d p (p - 1)).f (q + 1) u) =
    (A.d p (p - 1)).f q ((A.X p).d (q + 1) q u) at hh
  rw [← hh, hu]
  exact congrArg (fun f => f v) ((A.X (p - 1)).d_comp_d (q + 2) (q + 1) q)

/-- (blueprint: lem-weil-pbc-double-complex-row-cycle-lifts-to-zigzag)
In a first-quadrant homological double complex whose rows are exact in positive
horizontal degrees, every cycle in the cokernel of the first horizontal map
has a representative which extends to a zig-zag. The row-cokernel complex
`Aʳᵗ` is `A.opcycles 0`, formed in the abelian category of chain complexes:
its degree `q` is the cokernel of `d₁,ᵩ : A₁,ᵩ → A₀,ᵩ`, with projection
`π = A.pOpcycles 0` and differential induced by `δ`. The hypothesis `hcycle`
says that `πₙ(x)` is a cycle of `Aʳᵗ` (automatic at `n = 0`, where there is
no outgoing differential). Row exactness is `ShortComplex.Exact` of
`Aₚ₊₁,ᵩ → Aₚ,ᵩ → Aₚ₋₁,ᵩ` for `p ≥ 1`.

Source: Stacks Project, Algebra, Lemma Tag 00M1 (`lemma-no-spectral-sequence`),
proof lines 18464--18481. Proof, following the node's five steps:

1. If `n = 0`, take the tuple with sole entry `x`. The conditions defining
   `zigzagCycles` are empty (def-weil-pbc-double-complex-zigzag-module).
2. For `0 ≤ k ≤ n`, inductively construct entries `aⱼ,ₙ₋ⱼ` for `0 ≤ j ≤ k`,
   starting with `a₀,ₙ = x`, with `d aⱼ,ₙ₋ⱼ = δ aⱼ₋₁,ₙ₋ⱼ₊₁` for `1 ≤ j ≤ k`.
   The initial partial tuple consists just of `x`.
3. For `n > 0`, the cycle condition says that `δ x` belongs to the kernel of
   the projection onto the row cokernel, hence to the image of `d`. Choose
   `a₁,ₙ₋₁` with `d a₁,ₙ₋₁ = δ x` (def-weil-pbc-module-chain-complex-homology).
4. For `2 ≤ k ≤ n`, put `y = δ aₖ₋₁,ₙ₋ₖ₊₁`. Commutation gives
   `d y = δ d aₖ₋₁,ₙ₋ₖ₊₁ = δ δ aₖ₋₂,ₙ₋ₖ₊₂ = 0`. Row exactness at the
   positive horizontal position `k - 1` gives `aₖ,ₙ₋ₖ` with `d aₖ,ₙ₋ₖ = y`
   (def-weil-pbc-exact-sequence), preserving all previously chosen entries.
5. At `k = n`, assemble the finite tuple in `zigzagTotal A n`. Its adjacent
   equations are precisely those defining `zigzagCycles A n`, and its `(0,n)`
   component remains `x` (def-weil-pbc-double-complex-zigzag-module). -/
theorem row_cycle_lifts_to_zigzag
    (A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ)
    (x : (A.X 0).X n)
    (hcycle : ∃ c : (A.opcycles 0).cycles n,
      (A.opcycles 0).iCycles n c = (A.pOpcycles 0).f n x) :
    ∃ a : zigzagTotal A n,
      a ∈ zigzagCycles A n ∧
        DirectSum.component R (ZigzagIndex n)
          (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
          ⟨(0, n), by omega⟩ a = x := by
  classical
  have hpartial : ∀ k : ℕ, k ≤ n →
      ∃ b : ∀ p q : ℕ, (A.X p).X q,
        b 0 n = x ∧ ∀ p q : ℕ, p + 1 + q = n → p < k →
          (A.d (p + 1) p).f q (b (p + 1) q) =
            (A.X p).d (q + 1) q (b p (q + 1)) := by
    -- Keep previously chosen rows fixed while inserting one new antidiagonal entry.
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Function.update (fun p q => (0 : (A.X p).X q)) 0
        (Function.update (fun q => (0 : (A.X 0).X q)) n x), ?_, ?_⟩
      · simp
      · intro p q _ hp
        omega
    | succ k ih =>
      intro hk
      obtain ⟨b, hb, hrel⟩ := ih (by omega)
      let q := n - (k + 1)
      have hn : k + 1 + q = n := by dsimp [q]; omega
      have lift : ∃ y : (A.X (k + 1)).X q,
          (A.d (k + 1) k).f q y = (A.X k).d (q + 1) q (b k (q + 1)) := by
        cases k with
        | zero =>
          have hqn : q + 1 = n := by omega
          apply first_lift A q (b 0 (q + 1))
          rw [hqn, hb]
          exact hcycle
        | succ p =>
          apply next_lift A (p + 1) q (hrow _ _ (by omega))
            (b (p + 1) (q + 1)) (b p (q + 2))
          simpa using hrel p (q + 1) (by omega) (by omega)
      obtain ⟨y, hy⟩ := lift
      let b' := Function.update b (k + 1) (Function.update (b (k + 1)) q y)
      refine ⟨b', ?_, ?_⟩
      · simpa [b'] using hb
      · intro p t ht hp
        by_cases hpk : p = k
        · subst p
          have htq : t = q := by omega
          subst t
          simpa [b'] using hy
        · have hp1 : p + 1 ≠ k + 1 := by omega
          have hp0 : p ≠ k + 1 := by omega
          simpa [b', hpk, hp1, hp0] using hrel p t ht (by omega)
  -- The antidiagonal is finite, so this family defines an element of the direct sum.
  obtain ⟨b, hb, hrel⟩ := hpartial n le_rfl
  let : Fintype (ZigzagIndex n) := Fintype.ofInjective
    (fun i : ZigzagIndex n => (⟨i.1.1, by have := i.2; omega⟩ : Fin (n + 1)))
    (by intro i j hij; apply Subtype.ext; have := i.2; have := j.2
        have h := congrArg Fin.val hij; apply Prod.ext <;> dsimp at * <;> omega)
  let a : zigzagTotal A n := DFinsupp.equivFunOnFintype.symm
    (fun i : ZigzagIndex n => b i.1.1 i.1.2)
  refine ⟨a, ?_, ?_⟩
  · intro p q h
    change zigzagRelation A n p q h a = 0
    simp only [zigzagRelation, LinearMap.sub_apply, LinearMap.comp_apply]
    change (A.d (p + 1) p).f q (b (p + 1) q) -
      (A.X p).d (q + 1) q (b p (q + 1)) = 0
    exact sub_eq_zero.mpr (hrel p q h (by omega))
  · change b 0 n = x
    exact hb

end HomologicalComplex₂
