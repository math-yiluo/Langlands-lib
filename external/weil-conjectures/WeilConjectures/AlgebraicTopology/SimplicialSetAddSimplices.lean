/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-!
# An inclusion of finite simplicial sets is a chain of one-simplex extensions

Source: literature/stacks-project/simplicial.tex, Lemma 018S (auxiliary; not a blueprint node)
-/

@[expose] public section

open CategoryTheory Simplicial Limits
open Opposite

universe u

namespace SSet

private theorem exists_first_simplex
    {S : SSet.{u}} (U V : S.Subcomplex) (hUV : U ≤ V) (hne : U ≠ V) :
    ∃ (n : ℕ) (x : S.obj (op ⦋n⦌)), x ∈ V.obj (op ⦋n⦌) ∧
      x ∉ U.obj (op ⦋n⦌) ∧ x ∈ S.nonDegenerate n ∧
      ∀ (i : ℕ), i < n → V.obj (op ⦋i⦌) = U.obj (op ⦋i⦌) := by
  classical
  have hnot : ¬ V ≤ U := fun h ↦ hne (le_antisymm hUV h)
  rw [Subcomplex.le_iff_contains_nonDegenerate] at hnot
  push Not at hnot
  obtain ⟨m, y, hyV, hyU⟩ := hnot
  have hex : ∃ n : ℕ, ∃ x : S.obj (op ⦋n⦌), x ∈ V.obj _ ∧ x ∉ U.obj _ :=
    ⟨m, y.val, hyV, hyU⟩
  let n := Nat.find hex
  obtain ⟨x, hxV, hxU⟩ := Nat.find_spec hex
  have hbelow : ∀ (i : ℕ), i < n → V.obj (op ⦋i⦌) = U.obj (op ⦋i⦌) := by
    intro i hi
    apply le_antisymm
    · intro z hz
      by_contra h
      exact Nat.find_min hex hi ⟨z, hz, h⟩
    · exact hUV _
  refine ⟨n, x, hxV, hxU, ?_, hbelow⟩
  rw [mem_nonDegenerate_iff_notMem_degenerate]
  intro hx
  have hx' := (V.mem_degenerate_iff ⟨x, hxV⟩).mpr hx
  obtain ⟨i, hi, f, y, hy⟩ := hx'
  apply hxU
  have hyU : y.val ∈ U.obj (op ⦋i⦌) := by
    rw [← hbelow i hi]
    exact y.property
  have hmap := U.map f.op hyU
  have heq : S.map f.op y.val = x := congrArg Subtype.val hy
  exact heq ▸ hmap

private theorem first_extension_properties
    {S : SSet.{u}} (U V : S.Subcomplex) (hUV : U ≤ V)
    (n : ℕ) (x : S.obj (op ⦋n⦌)) (hxV : x ∈ V.obj (op ⦋n⦌))
    (hbelow : ∀ (i : ℕ), i < n → V.obj (op ⦋i⦌) = U.obj (op ⦋i⦌)) :
    let W := U ⊔ Subcomplex.ofSimplex x
    W ≤ V ∧
      (∀ (i : ℕ), i < n → W.obj (op ⦋i⦌) = U.obj (op ⦋i⦌)) ∧
      W.obj (op ⦋n⦌) = U.obj (op ⦋n⦌) ∪ {x} ∧
      ∀ (j : ℕ) (z : W.toSSet.obj (op ⦋j⦌)), n < j →
        z.val ∉ U.obj (op ⦋j⦌) → z ∈ W.toSSet.degenerate j := by
  classical
  dsimp only
  let W := U ⊔ Subcomplex.ofSimplex x
  have hWV : W ≤ V := sup_le hUV ((Subcomplex.ofSimplex_le_iff x V).mpr hxV)
  have hlow : ∀ (i : ℕ), i < n → W.obj (op ⦋i⦌) = U.obj (op ⦋i⦌) := by
    intro i hi
    exact le_antisymm ((hWV _).trans (hbelow i hi).le) ((le_sup_left : U ≤ W) _)
  refine ⟨hWV, hlow, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro z hz
      change z ∈ W.obj (op ⦋n⦌) at hz
      by_cases hzU : z ∈ U.obj (op ⦋n⦌)
      · exact Or.inl hzU
      · right
        have hzgen : z ∈ (Subcomplex.ofSimplex x).obj (op ⦋n⦌) := hz.resolve_left hzU
        obtain ⟨f, hf⟩ := (Subcomplex.mem_ofSimplex_obj_iff x z).mp hzgen
        by_cases hznd : z ∈ S.nonDegenerate n
        · have := S.mono_of_nonDegenerate ⟨z, hznd⟩ f x hf
          obtain rfl := SimplexCategory.eq_id_of_mono f
          simpa using hf.symm
        · exfalso
          have hzdeg : z ∈ S.degenerate n :=
            (S.mem_degenerate_iff_notMem_nonDegenerate z).mpr hznd
          have hzdeg' := (W.mem_degenerate_iff ⟨z, hz⟩).mpr hzdeg
          obtain ⟨i, hi, g, y, hy⟩ := hzdeg'
          have hyU : y.val ∈ U.obj (op ⦋i⦌) := by
            rw [← hlow i hi]
            exact y.property
          have hmap := U.map g.op hyU
          have heq : S.map g.op y.val = z := congrArg Subtype.val hy
          exact hzU (heq ▸ hmap)
    · rintro z (hz | hz)
      · exact Or.inl hz
      · have : z = x := hz
        subst z
        exact Or.inr (Subcomplex.mem_ofSimplex_obj x)
  · intro j z hj hzU
    rw [W.mem_degenerate_iff, S.mem_degenerate_iff_notMem_nonDegenerate]
    intro hznd
    have hzgen : z.val ∈ (Subcomplex.ofSimplex x).obj (op ⦋j⦌) :=
      z.property.resolve_left hzU
    obtain ⟨f, hf⟩ := (Subcomplex.mem_ofSimplex_obj_iff x z.val).mp hzgen
    have := S.mono_of_nonDegenerate ⟨z.val, hznd⟩ f x hf
    have hlen : j ≤ n := SimplexCategory.len_le_of_mono f
    omega

private def SimplexExtension {S : SSet.{u}} (A B : S.Subcomplex) : Prop :=
  ∃ (n : ℕ) (x : B.toSSet.obj (op ⦋n⦌)),
    x.val ∉ A.obj (op ⦋n⦌) ∧
    (∀ (i : ℕ), i < n → B.obj (op ⦋i⦌) = A.obj (op ⦋i⦌)) ∧
    B.obj (op ⦋n⦌) = A.obj (op ⦋n⦌) ∪ {x.val} ∧
    ∀ (j : ℕ) (z : B.toSSet.obj (op ⦋j⦌)), n < j →
      z.val ∉ A.obj (op ⦋j⦌) → z ∈ B.toSSet.degenerate j

private def SimplexChain {S : SSet.{u}} (A B : S.Subcomplex) : Prop :=
  ∃ (r : ℕ) (W : Fin (r + 1) → S.Subcomplex),
    W 0 = A ∧ W ⟨r, Nat.lt_succ_self r⟩ = B ∧
    (∀ k : Fin r, W k.castSucc ≤ W k.succ) ∧
    ∀ k : Fin r, SimplexExtension (W k.castSucc) (W k.succ)

private theorem simplexChain_refl {S : SSet.{u}} (A : S.Subcomplex) :
    SimplexChain A A := by
  exact ⟨0, fun _ ↦ A, rfl, rfl, Fin.elim0, Fin.elim0⟩

private theorem simplexChain_prepend {S : SSet.{u}} {A B C : S.Subcomplex}
    (hAB : A ≤ B) (hstep : SimplexExtension A B) (hchain : SimplexChain B C) :
    SimplexChain A C := by
  obtain ⟨r, W, hfirst, hlast, hmono, hsteps⟩ := hchain
  refine ⟨r + 1, Fin.cons A W, rfl, ?_, ?_, ?_⟩
  · exact hlast
  · intro k
    refine Fin.cases ?_ (fun i ↦ ?_) k
    · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hfirst] using hAB
    · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hmono i
  · intro k
    refine Fin.cases ?_ (fun i ↦ ?_) k
    · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hfirst] using hstep
    · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hsteps i

private theorem simplexChain_exists {S : SSet.{u}} (V : S.Subcomplex)
    [SSet.Finite V.toSSet] (U : S.Subcomplex) (hUV : U ≤ V) :
    SimplexChain U V := by
  classical
  let : Fintype V.toSSet.N := Fintype.ofFinite _
  let missing (A : S.Subcomplex) : Finset V.toSSet.N :=
    Finset.univ.filter (fun s ↦ s.simplex.val ∉ A.obj (op ⦋s.dim⦌))
  induction hm : (missing U).card using Nat.strong_induction_on generalizing U with
  | h m ih =>
    by_cases hEq : U = V
    · subst U
      exact simplexChain_refl V
    obtain ⟨n, x, hxV, hxU, hxnd, hbelow⟩ := exists_first_simplex U V hUV hEq
    let W := U ⊔ Subcomplex.ofSimplex x
    obtain ⟨hWV, hlow, hdegree, hhigh⟩ :=
      first_extension_properties U V hUV n x hxV hbelow
    have hUW : U ≤ W := le_sup_left
    have hstep : SimplexExtension U W :=
      ⟨n, ⟨x, Or.inr (Subcomplex.mem_ofSimplex_obj x)⟩, hxU, hlow, hdegree, hhigh⟩
    have hss : missing W ⊂ missing U := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro s hs
        simp only [missing, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        exact fun hu ↦ hs (hUW _ hu)
      · intro heq
        let s : V.toSSet.N := N.mk ⟨x, hxV⟩
          ((V.mem_nonDegenerate_iff ⟨x, hxV⟩).mpr hxnd)
        have hsU : s ∈ missing U := by
          simpa [missing, s, N.mk] using hxU
        have hsW : s ∉ missing W := by
          simp only [missing, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          exact Or.inr (Subcomplex.mem_ofSimplex_obj x)
        exact hsW (heq.symm ▸ hsU)
    apply simplexChain_prepend hUW hstep
    apply ih (missing W).card
    · rw [← hm]
      exact Finset.card_lt_card hss
    · exact hWV
    · rfl

private theorem range_inclusion {S : SSet.{u}} (A : S.Subcomplex)
    (i : SimplexCategoryᵒᵖ) : Set.range (A.ι.app i) = A.obj i := by
  ext x
  exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

set_option linter.unusedVariables false in
/-- An inclusion of finite simplicial sets can be built by adjoining one simplex
at a time. Source: literature/stacks-project/simplicial.tex, Lemma 018S, with
Lemma 018R (auxiliary; not a blueprint node).
The proof proceeds by induction on the finite set of nondegenerate simplices
of `V` outside `U`. Every simplex is an iterated degeneracy of a
nondegenerate one, so containing all such simplices forces equality. For the
induction step choose a missing nondegenerate simplex `x` of least degree
`n`; all lower-degree simplices already lie in `U`. Adjoin to `U` all
degeneracies of `x`. The surjection-injection factorization in the simplex
category and the simplicial identities show that this is a subcomplex, adds
nothing below `n`, adds exactly `x` in degree `n`, and adds only degenerate
simplices above `n`. It remains finite and nonempty in every degree, and has
one fewer missing nondegenerate simplex. Applying the induction hypothesis
and prepending this first extension gives the displayed chain. -/
theorem add_simplices
    (S : SSet.{u})
    (U V : S.Subcomplex)
    (hUV : U ≤ V)
    (hU_fin : ∀ (n : ℕ), Finite ((U : SSet).obj (Opposite.op (SimplexCategory.mk n))))
    (hV_fin : ∀ (n : ℕ), Finite ((V : SSet).obj (Opposite.op (SimplexCategory.mk n))))
    (hU_nonempty : ∀ (n : ℕ), Nonempty ((U : SSet).obj (Opposite.op (SimplexCategory.mk n))))
    (hV_nonempty : ∀ (n : ℕ), Nonempty ((V : SSet).obj (Opposite.op (SimplexCategory.mk n))))
    [SSet.Finite (U : SSet)] [SSet.Finite (V : SSet)] :
    ∃ (r : ℕ) (W : Fin (r + 1) → S.Subcomplex),
      W 0 = U ∧ W ⟨r, Nat.lt_succ_self r⟩ = V ∧
      (∀ (k : Fin r), W k.castSucc ≤ W k.succ) ∧
      (∀ (k : Fin r), ∃ (n : ℕ) (x : (W k.succ : SSet).obj
          (Opposite.op (SimplexCategory.mk n))),
        x.1 ∉ Set.range ((W k.castSucc).ι.app
          (Opposite.op (SimplexCategory.mk n))) ∧
        (∀ (i : ℕ), i < n →
          Set.range ((W k.succ).ι.app (Opposite.op (SimplexCategory.mk i))) =
            Set.range ((W k.castSucc).ι.app (Opposite.op (SimplexCategory.mk i)))) ∧
        Set.range ((W k.succ).ι.app (Opposite.op (SimplexCategory.mk n))) =
          Set.range ((W k.castSucc).ι.app (Opposite.op (SimplexCategory.mk n))) ∪ {x.1} ∧
        (∀ (j : ℕ) (z : (W k.succ : SSet).obj
            (Opposite.op (SimplexCategory.mk j))), n < j →
          z.1 ∉ Set.range ((W k.castSucc).ι.app
            (Opposite.op (SimplexCategory.mk j))) →
          z ∈ SSet.degenerate (W k.succ : SSet) j)) := by
  obtain ⟨r, W, hfirst, hlast, hmono, hsteps⟩ := simplexChain_exists V U hUV
  refine ⟨r, W, hfirst, hlast, hmono, ?_⟩
  intro k
  obtain ⟨n, x, hx, hlow, hdegree, hhigh⟩ := hsteps k
  refine ⟨n, x, ?_, ?_, ?_, ?_⟩
  · simpa only [range_inclusion] using hx
  · intro i hi
    simpa only [range_inclusion] using hlow i hi
  · simpa only [range_inclusion] using hdegree
  · intro j z hj hz
    apply hhigh j z hj
    simpa only [range_inclusion] using hz

end SSet
