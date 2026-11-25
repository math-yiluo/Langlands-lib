/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import WeilConjectures.AlgebraicGeometry.AlternatingCechPartialSortUnique
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Unsigned correspondence for tail deletions

Source: Stacks Project, Tag 01FM, verification of equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-correspondence)
-/

@[expose] public section

set_option autoImplicit false

universe v

namespace AlgebraicGeometry.Scheme

/-- Filtered outgoing tail indices, retaining original labels.
Source: Stacks 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-correspondence) -/
abbrev cechTailOutgoingIndex {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :=
  {x : Equiv.Perm (Fin (p + 2)) × Fin (p + 2) ×
      Equiv.Perm (Fin (p + 2)) × Fin (p + 3) //
    ((cechStableSort t x.1 ∧ cechPartialSort x.1 x.2.2.1 x.2.1) ∧
      cechJunction x.1 x.2.2.1 x.2.1 x.2.2.2 ≠ x.1 x.2.1) ∧
      ¬ x.2.2.2.val < x.2.1.val}

/-- Filtered incoming indices whose omitted label follows the junction in stable order.
Source: Stacks 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-correspondence) -/
abbrev cechTailIncomingIndex {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :=
  {y : Fin (p + 2) × Equiv.Perm (Fin (p + 1)) × Fin (p + 1) ×
      Equiv.Perm (Fin (p + 1)) //
    (cechStableSort (t ∘ y.1.succAbove) y.2.1 ∧
      cechPartialSort y.2.1 y.2.2.2 y.2.2.1) ∧
      ¬ (t y.1 < t (y.1.succAbove (y.2.1 y.2.2.1)) ∨
        (t y.1 = t (y.1.succAbove (y.2.1 y.2.2.1)) ∧
          y.1 < y.1.succAbove (y.2.1 y.2.2.1)))}

private def deletePerm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv k).trans
    ((σ.subtypeEquiv (p := fun i => i ≠ k) (q := fun j => j ≠ σ k)
      (fun _ => σ.injective.ne_iff.symm)).trans (finSuccAboveEquiv (σ k)).symm)

private theorem deletePerm_spec {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) (z : Fin n) :
    (σ k).succAbove (deletePerm σ k z) = σ (k.succAbove z) := by
  have h := (finSuccAboveEquiv (σ k)).apply_symm_apply
    ((σ.subtypeEquiv (p := fun i => i ≠ k) (q := fun j => j ≠ σ k)
      (fun _ => σ.injective.ne_iff.symm)) (finSuccAboveEquiv k z))
  exact congrArg Subtype.val h

private theorem stable_delete {I : Type v} [LinearOrder I] {n : ℕ}
    (t : Fin (n + 1) → I) (σ : Equiv.Perm (Fin (n + 1)))
    (hs : cechStableSort t σ) (k : Fin (n + 1)) :
    cechStableSort (t ∘ (σ k).succAbove) (deletePerm σ k) := by
  constructor
  · intro i j hij
    change t ((σ k).succAbove (deletePerm σ k i)) ≤
      t ((σ k).succAbove (deletePerm σ k j))
    rw [deletePerm_spec, deletePerm_spec]
    exact hs.1 ((Fin.strictMono_succAbove k).monotone hij)
  · intro i j hij ht
    apply (Fin.strictMono_succAbove (σ k)).lt_iff_lt.mp
    rw [deletePerm_spec, deletePerm_spec]
    apply hs.2 _ _ ((Fin.strictMono_succAbove k) hij)
    simpa only [Function.comp_apply, deletePerm_spec] using ht

private theorem stable_unique {I : Type v} [LinearOrder I] {n : ℕ}
    (t : Fin n → I) (σ ρ : Equiv.Perm (Fin n))
    (hσ : cechStableSort t σ) (hρ : cechStableSort t ρ) : σ = ρ :=
  (Tuple.eq_sort_iff.mpr hσ).trans (Tuple.eq_sort_iff.mpr hρ).symm

private theorem outgoing_rank {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (x : cechTailOutgoingIndex p t)
    (k : Fin (p + 2)) (hk : k.val + 1 = x.val.2.2.2.val) :
    x.val.2.1.val ≤ k.val ∧ x.val.2.1 < x.val.1.symm (x.val.2.2.1 k) := by
  rcases x with ⟨⟨σ, a, τ, r⟩, ⟨⟨hs, ht⟩, hn⟩, hr⟩
  dsimp only at hk hn hr hs ht ⊢
  have har : a.val < r.val := by
    have hne : a.val ≠ r.val := by
      intro he
      apply hn
      simp only [cechJunction]
      rw [dite_eq_left (by omega)]
      congr 1
      exact Fin.ext he.symm
    omega
  have hka : a.val ≤ k.val := by omega
  have hnk : τ k ≠ σ a := by
    intro he
    apply hn
    simp only [cechJunction]
    rw [dite_eq_right (by omega)]
    convert he using 1
    congr 1
    apply Fin.ext
    change r.val - 1 = k.val
    omega
  refine ⟨hka, ?_⟩
  by_contra hd
  have hd' : (σ.symm (τ k)).val ≤ a.val := le_of_not_gt hd
  rcases hd'.eq_or_lt with he | hl
  · apply hnk
    have he' : σ.symm (τ k) = a := Fin.ext he
    exact σ.symm_apply_eq.mp he'
  · have ht' := ht.1 (σ.symm (τ k)) hl
    rw [σ.apply_symm_apply] at ht'
    have he := τ.injective ht'
    have hev := congrArg Fin.val he
    omega

private theorem partial_unique {n : ℕ} (σ τ η : Equiv.Perm (Fin n))
    (a : Fin n) (hτ : cechPartialSort σ τ a) (hη : cechPartialSort σ η a) :
    τ = η := by
  obtain ⟨π, _, hπ⟩ := cechPartialSort_existsUnique n σ a.val (by omega)
  exact (hπ τ hτ).trans (hπ η hη).symm

private theorem stable_compare {I : Type v} [LinearOrder I] {n : ℕ}
    (t : Fin n → I) (σ : Equiv.Perm (Fin n)) (hs : cechStableSort t σ)
    (i j : Fin n) :
    i < j ↔ t (σ i) < t (σ j) ∨ (t (σ i) = t (σ j) ∧ σ i < σ j) := by
  constructor
  · intro hij
    rcases (hs.1 hij.le).lt_or_eq with ht | ht
    · exact Or.inl ht
    · exact Or.inr ⟨ht, hs.2 i j hij ht⟩
  · intro h
    by_contra hn
    have hji : j ≤ i := le_of_not_gt hn
    rcases hji.eq_or_lt with he | hl
    · subst i
      rcases h with h | ⟨_, h⟩ <;> exact (lt_irrefl _ h)
    · have ht := hs.1 hl.le
      rcases h with h | ⟨he, h⟩
      · exact (not_lt_of_ge ht h)
      · exact (not_lt_of_ge (hs.2 j i hl he.symm).le h)

private theorem partial_delete {n : ℕ} (σ τ : Equiv.Perm (Fin (n + 1)))
    (a k d : Fin (n + 1)) (b : Fin n) (ht : cechPartialSort σ τ a)
    (hb : b.val = a.val) (hk : a.val ≤ k.val) (hd : a < d)
    (hj : σ d = τ k) :
    cechPartialSort (deletePerm σ d) (deletePerm τ k) b := by
  constructor
  · intro i hi
    apply (Fin.strictMono_succAbove (τ k)).injective
    rw [deletePerm_spec, ← hj, deletePerm_spec]
    have hki : k.succAbove i = i.castSucc := by
      apply Fin.succAbove_of_castSucc_lt
      change i.val < k.val
      omega
    have hdi : d.succAbove i = i.castSucc := by
      apply Fin.succAbove_of_castSucc_lt
      change i.val < d.val
      change a.val < d.val at hd
      omega
    rw [hki, hdi]
    exact ht.1 _ (by simp only [Fin.val_castSucc]; omega)
  · intro i j hi hij
    apply (Fin.strictMono_succAbove (τ k)).lt_iff_lt.mp
    rw [deletePerm_spec, deletePerm_spec]
    apply ht.2 _ _ ?_ ((Fin.strictMono_succAbove k) hij)
    simp only [Fin.succAbove]
    split <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

private theorem outgoing_positive {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (x : cechTailOutgoingIndex p t) :
    0 < x.val.2.2.2.val := by
  have hn := x.property.1.2
  have hr := x.property.2
  by_contra h
  have he : x.val.2.2.2.val = x.val.2.1.val := by omega
  apply hn
  simp only [cechJunction]
  rw [dite_eq_left (by omega)]
  congr 1
  exact Fin.ext he

private def outgoing_position {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (x : cechTailOutgoingIndex p t) : Fin (p + 2) :=
  ⟨x.val.2.2.2.val - 1, by have := outgoing_positive p t x; omega⟩

private theorem outgoing_position_spec {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (x : cechTailOutgoingIndex p t) :
    (outgoing_position p t x).val + 1 = x.val.2.2.2.val := by
  have := outgoing_positive p t x
  dsimp only [outgoing_position]
  omega

private def tail_delete {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (x : cechTailOutgoingIndex p t) :
    cechTailIncomingIndex p t := by
  let σ := x.val.1
  let a := x.val.2.1
  let τ := x.val.2.2.1
  let k := outgoing_position p t x
  let j := τ k
  let d := σ.symm j
  have hk := outgoing_position_spec p t x
  have hka := (outgoing_rank p t x k hk).1
  have had := (outgoing_rank p t x k hk).2
  let b : Fin (p + 1) := ⟨a.val, by
    change a.val < d.val at had
    have := d.isLt
    omega⟩
  have hdj : σ d = j := σ.apply_symm_apply j
  let ρ := deletePerm σ d
  let η := deletePerm τ k
  refine ⟨(j, ρ, b, η), ⟨?_, ?_⟩, ?_⟩
  · simpa only [hdj] using stable_delete t σ x.property.1.1.1 d
  · exact partial_delete σ τ a k d b x.property.1.1.2 rfl hka had hdj
  · have hdb : d.succAbove b = a := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by
        change b.val < d.val
        exact had)]
      rfl
    have hρ : j.succAbove (ρ b) = σ a := by
      simpa only [ρ, hdj, hdb] using deletePerm_spec σ d b
    rw [hρ]
    intro h
    have hda := (stable_compare t σ x.property.1.1.1 d a).mpr (by
      simpa only [hdj] using h)
    exact (not_lt_of_ge had.le hda)

private theorem tail_delete_spec {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (x : cechTailOutgoingIndex p t) :
    ∃ k : Fin (p + 2),
      k.val + 1 = x.val.2.2.2.val ∧
      x.val.2.2.1 k = (tail_delete p t x).val.1 ∧
      (∀ z, x.val.2.2.1 (k.succAbove z) =
        (tail_delete p t x).val.1.succAbove ((tail_delete p t x).val.2.2.2 z)) ∧
      x.val.2.1.val = (tail_delete p t x).val.2.2.1.val := by
  refine ⟨outgoing_position p t x, outgoing_position_spec p t x, rfl, ?_, rfl⟩
  intro z
  exact (deletePerm_spec x.val.2.2.1 (outgoing_position p t x) z).symm

private theorem tail_delete_injective {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) : Function.Injective (tail_delete p t) := by
  intro x x' he
  obtain ⟨k, hk, hj, _, ha⟩ := tail_delete_spec p t x
  obtain ⟨k', hk', hj', _, ha'⟩ := tail_delete_spec p t x'
  have hσ : x.val.1 = x'.val.1 :=
    stable_unique t _ _ x.property.1.1.1 x'.property.1.1.1
  have hav : x.val.2.1.val = x'.val.2.1.val := by
    rw [ha, ha', he]
  have haeq : x.val.2.1 = x'.val.2.1 := Fin.ext hav
  have hτ : x.val.2.2.1 = x'.val.2.2.1 := by
    apply partial_unique x.val.1 _ _ x.val.2.1 x.property.1.1.2
    simpa only [hσ, haeq] using x'.property.1.1.2
  have hkk : k = k' := by
    apply x.val.2.2.1.injective
    rw [hj, hτ, hj', he]
  have hr : x.val.2.2.2 = x'.val.2.2.2 := Fin.ext (by omega)
  apply Subtype.ext
  exact Prod.ext hσ (Prod.ext haeq (Prod.ext hτ hr))

private theorem tail_delete_surjective {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) : Function.Surjective (tail_delete p t) := by
  intro y
  let j := y.val.1
  let ρ := y.val.2.1
  let b := y.val.2.2.1
  let η := y.val.2.2.2
  let σ := Tuple.sort t
  have hs : cechStableSort t σ := Tuple.eq_sort_iff.mp rfl
  let d := σ.symm j
  have hdj : σ d = j := σ.apply_symm_apply j
  have hρ : deletePerm σ d = ρ := by
    apply stable_unique (t ∘ j.succAbove)
    · simpa only [hdj] using stable_delete t σ hs d
    · exact y.property.1.1
  have hdel : σ (d.succAbove b) = j.succAbove (ρ b) := by
    simpa only [hdj, hρ] using (deletePerm_spec σ d b).symm
  have hbd : b.val < d.val := by
    have hnot : ¬ d < d.succAbove b := by
      intro h
      apply y.property.2
      simpa only [hdj, hdel] using (stable_compare t σ hs d (d.succAbove b)).mp h
    have hne : d.succAbove b ≠ d := Fin.succAbove_ne d b
    have hlt : d.succAbove b < d := lt_of_le_of_ne (le_of_not_gt hnot) hne
    exact (Fin.succAbove_lt_iff_castSucc_lt d b).mp hlt
  let a : Fin (p + 2) := b.castSucc
  have had : a < d := hbd
  obtain ⟨τ, ht, _⟩ := cechPartialSort_existsUnique (p + 2) σ a.val (by omega)
  let k := τ.symm j
  have hτk : τ k = j := τ.apply_symm_apply j
  have hka : a.val ≤ k.val := by
    by_contra hn
    have hpre := ht.1 k (lt_of_not_ge hn)
    rw [hτk] at hpre
    have hkd : k = d := σ.injective (hpre.symm.trans hdj.symm)
    have hkv := congrArg Fin.val hkd
    change a.val < d.val at had
    omega
  have hη : deletePerm τ k = η := by
    apply partial_unique ρ _ _ b ?_ y.property.1.2
    rw [← hρ]
    exact partial_delete σ τ a k d b ht rfl hka (by exact had) (hdj.trans hτk.symm)
  let r : Fin (p + 3) := k.succ
  have hnj : cechJunction σ τ a r ≠ σ a := by
    simp only [cechJunction]
    rw [dite_eq_right (by change ¬ k.val + 1 ≤ a.val; omega)]
    intro he
    have hek : (⟨r.val - 1, by omega⟩ : Fin (p + 2)) = k := Fin.ext (by
      change k.val + 1 - 1 = k.val
      omega)
    rw [hek, hτk] at he
    have hda := σ.injective (hdj.trans he)
    exact had.ne hda.symm
  let x : cechTailOutgoingIndex p t :=
    ⟨(σ, a, τ, r), ⟨⟨hs, ht⟩, hnj⟩, by
      change ¬ k.val + 1 < a.val
      omega⟩
  refine ⟨x, ?_⟩
  have hxk : outgoing_position p t x = k := by
    apply Fin.ext
    change k.val + 1 - 1 = k.val
    omega
  apply Subtype.ext
  change (tail_delete p t x).val = (j, ρ, b, η)
  dsimp only [tail_delete]
  simp only [hxk]
  dsimp only [x, d]
  rw [hτk, hρ, hη]
  rfl

/-- The deletion correspondence with the rank, restriction, and prefix identities.
Proof: construct deletion and insertion maps on the finite permutations and verify their
properties by the defining cases of stable and partial sorting.
Source: Stacks Project, Tag 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-basic) -/
theorem cechTailDeletionBasic {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :
    ∃ e : cechTailOutgoingIndex p t ≃ cechTailIncomingIndex p t,
      ∀ x, ∃ k : Fin (p + 2),
        k.val + 1 = x.val.2.2.2.val ∧
        x.val.2.2.1 k = (e x).val.1 ∧
        (∀ z, x.val.2.2.1 (k.succAbove z) =
          (e x).val.1.succAbove ((e x).val.2.2.2 z)) ∧
        x.val.2.1.val = (e x).val.2.2.1.val := by
  classical
  let e := Equiv.ofBijective (tail_delete p t)
    ⟨tail_delete_injective p t, tail_delete_surjective p t⟩
  exact ⟨e, tail_delete_spec p t⟩

/-- The junction-map identity for the basic tail deletion correspondence.
Proof: use the deletion identities to check the two cases in the definition of the
junction map, giving equality on every finite position.
Source: Stacks Project, Tag 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-junction) -/
theorem cechTailDeletionJunction {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (e : cechTailOutgoingIndex p t ≃ cechTailIncomingIndex p t)
    (he : ∀ x, ∃ k : Fin (p + 2),
      k.val + 1 = x.val.2.2.2.val ∧
      x.val.2.2.1 k = (e x).val.1 ∧
      (∀ z, x.val.2.2.1 (k.succAbove z) =
        (e x).val.1.succAbove ((e x).val.2.2.2 z)) ∧
      x.val.2.1.val = (e x).val.2.2.1.val)
    (x : cechTailOutgoingIndex p t) :
    cechJunction x.val.1 x.val.2.2.1 x.val.2.1 ∘ x.val.2.2.2.succAbove =
      (e x).val.1.succAbove ∘
        cechJunction (e x).val.2.1 (e x).val.2.2.2 (e x).val.2.2.1 := by
  obtain ⟨k, hk, hj, hτ, ha⟩ := he x
  obtain ⟨hka, hda⟩ := outgoing_rank p t x k hk
  let σ := x.val.1
  let τ := x.val.2.2.1
  let a := x.val.2.1
  let r := x.val.2.2.2
  let y := e x
  let j := y.val.1
  let ρ := y.val.2.1
  let b := y.val.2.2.1
  let η := y.val.2.2.2
  let d := σ.symm j
  have hdj : σ d = j := σ.apply_symm_apply j
  have hdb : a.val < d.val := by
    dsimp only [a, d, σ, j, y]
    rwa [← hj]
  have hρ : deletePerm σ d = ρ := by
    apply stable_unique (t ∘ j.succAbove)
    · simpa only [hdj] using stable_delete t σ x.property.1.1.1 d
    · exact y.property.1.1
  have hp (z : Fin (p + 1)) (hz : z.val ≤ b.val) :
      σ ⟨z.val, by omega⟩ = j.succAbove (ρ z) := by
    have hs := deletePerm_spec σ d z
    have hdz : d.succAbove z = ⟨z.val, by omega⟩ := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by
        simp only [Fin.lt_def, Fin.val_castSucc]
        dsimp only [a, b, y] at hdb hz
        omega)]
      rfl
    rw [hdj, hρ, hdz] at hs
    exact hs.symm
  funext z
  change cechJunction σ τ a (r.succAbove z) = j.succAbove (cechJunction ρ η b z)
  by_cases hz : z.val ≤ b.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by
      simp only [Fin.lt_def, Fin.val_castSucc]
      dsimp only [r, b, y, a] at *
      omega)]
    simp only [cechJunction, Fin.val_castSucc]
    rw [dite_eq_left (by dsimp only [a, b, y] at *; omega), dite_eq_left hz]
    exact hp ⟨z.val, by omega⟩ hz
  · simp only [cechJunction]
    rw [dite_eq_right hz]
    by_cases hzr : z.val < r.val
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by exact hzr)]
      simp only [Fin.val_castSucc]
      rw [dite_eq_right (by dsimp only [a, b, y] at *; omega)]
      have h := hτ ⟨z.val - 1, by omega⟩
      rw [Fin.succAbove_of_castSucc_lt _ _ (by
        simp only [Fin.lt_def, Fin.val_castSucc]
        dsimp only [r] at hzr
        omega)] at h
      exact h
    · rw [Fin.succAbove_of_le_castSucc _ _ (by exact le_of_not_gt hzr)]
      simp only [Fin.val_succ]
      rw [dite_eq_right (by dsimp only [a, b, y] at *; omega)]
      have h := hτ ⟨z.val - 1, by omega⟩
      rw [Fin.succAbove_of_le_castSucc _ _ (by
        simp only [Fin.le_def, Fin.val_castSucc]
        dsimp only [r] at hzr
        omega)] at h
      convert h using 1
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega


/-- (blueprint: lem-pc-alternating-cech-tail-deletion-correspondence) -/
theorem cechTailDeletionCorrespondence {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :
    ∃ e : cechTailOutgoingIndex p t ≃ cechTailIncomingIndex p t,
      ∀ x, ∃ k : Fin (p + 2),
        k.val + 1 = x.val.2.2.2.val ∧
        x.val.2.2.1 k = (e x).val.1 ∧
        (∀ z, x.val.2.2.1 (k.succAbove z) =
          (e x).val.1.succAbove ((e x).val.2.2.2 z)) ∧
        x.val.2.1.val = (e x).val.2.2.1.val ∧
        cechJunction x.val.1 x.val.2.2.1 x.val.2.1 ∘ x.val.2.2.2.succAbove =
          (e x).val.1.succAbove ∘
      cechJunction (e x).val.2.1 (e x).val.2.2.2 (e x).val.2.2.1 := by
  obtain ⟨e, he⟩ := cechTailDeletionBasic p t
  refine ⟨e, ?_⟩
  intro x
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := he x
  have hk5 := cechTailDeletionJunction p t e he x
  exact ⟨k, hk1, hk2, hk3, hk4, hk5⟩


end AlgebraicGeometry.Scheme
