/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.Convergence

/-!
# Degenerate spectral sequences of exact couples

If from some page on the spectral sequence of a convergent exact couple is concentrated in the
column `p = 0`, then all later differentials vanish and the edge map from the abutment to that
column is an isomorphism (`CategoryTheory.ExactCouple.edge_collapse`,
`CategoryTheory.ExactCouple.isIso_edge`).

## Main definitions

- `CategoryTheory.ExactCouple.derivedIterSuccEIso`, `CategoryTheory.ExactCouple.derivedIterAddEIso`:
  an entry without incoming and outgoing differentials is unchanged on the later pages.
- `CategoryTheory.ExactCouple.ConvergenceData.edge`: the edge map `Aⁿ ⟶ E^{0, n}`.

## Main statements

- `CategoryTheory.ExactCouple.isZero_derivedIter_E`: vanishing entries stay zero on later pages.
- `CategoryTheory.ExactCouple.edge_collapse`, `CategoryTheory.ExactCouple.isIso_edge`: the edge
  collapse.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DecreasingFiltration

variable {A : C} (F : DecreasingFiltration A)

/-- If the graded piece `grᵖ` vanishes, then `Fᵖ⁺¹ = Fᵖ`. -/
lemma F_succ_eq_of_isZero_gr (p : ℤ) (h : IsZero (F.gr p)) : F.F (p + 1) = F.F p := by
  refine le_antisymm (F.F_succ_le p) ?_
  have : Epi (Subobject.ofLE _ _ (F.F_succ_le p)) :=
    (ShortComplex.exact_cokernel _).epi_f (h.eq_of_tgt _ _)
  have : IsIso (Subobject.ofLE _ _ (F.F_succ_le p)) := isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ (F.F_succ_le p))) (by simp)

/-- A filtration with `Fᴺ = 0` whose graded pieces vanish in degrees `≥ p` has `Fᵖ = 0`. -/
lemma F_eq_bot_of_isZero_gr (N p : ℤ) (hN : F.F N = ⊥) (h : ∀ k ≥ p, IsZero (F.gr k)) :
    F.F p = ⊥ := by
  by_cases hpN : N ≤ p
  · exact eq_bot_iff.mpr ((F.antitone hpN).trans hN.le)
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, p + k = N := ⟨(N - p).toNat, by omega⟩
    clear hpN
    induction k generalizing p with
    | zero =>
      obtain rfl : p = N := by simpa using hk
      exact hN
    | succ k ih =>
      rw [← F.F_succ_eq_of_isZero_gr p (h p le_rfl)]
      exact ih (p + 1) (fun l hl ↦ h l (by omega)) (by push_cast at hk; omega)

/-- A filtration with `Fᵐ = A` whose graded pieces vanish in degrees `< p` has `Fᵖ = A`. -/
lemma F_eq_top_of_isZero_gr (m p : ℤ) (hm : F.F m = ⊤) (h : ∀ k < p, IsZero (F.gr k)) :
    F.F p = ⊤ := by
  by_cases hmp : p ≤ m
  · exact eq_top_iff.mpr (hm.ge.trans (F.antitone hmp))
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m + k = p := ⟨(p - m).toNat, by omega⟩
    clear hmp
    induction k generalizing p with
    | zero =>
      obtain rfl : p = m := by simpa using hk.symm
      exact hm
    | succ k ih =>
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [F.F_succ_eq_of_isZero_gr q (h q (by omega))]
      exact ih q (fun l hl ↦ h l (by omega)) (by push_cast at hk; omega)


end DecreasingFiltration

namespace ExactCouple

variable {κ : Type w} [AddCommGroup κ] {a b c : κ} (X : ExactCouple C a b c)

/-- Vanishing entries of the spectral sequence of a couple stay zero on the later pages, the
pages being subquotients of the earlier ones. -/
lemma isZero_derivedIter_E (N M : ℕ) (hNM : N ≤ M) (i : κ)
    (h : IsZero ((X.derivedIter N).E i)) : IsZero ((X.derivedIter M).E i) := by
  induction M, hNM using Nat.le_induction with
  | base => exact h
  | succ M _ ih =>
    exact ShortComplex.isZero_homology_of_isZero_X₂ _ ih

/-- An entry of the spectral sequence of a couple which has no incoming and no outgoing
differential is unchanged on the next page. -/
noncomputable def derivedIterSuccEIso (N : ℕ) (i : κ)
    (hout : (X.derivedIter N).d i (i + (b + degIter a c N)) = 0)
    (hin : (X.derivedIter N).d (i - (b + degIter a c N)) i = 0) :
    (X.derivedIter (N + 1)).E i ≅ (X.derivedIter N).E i :=
  ((X.derivedIter N).dComplex.isoHomologyπ _ i (dComplex_prev i) hin).symm ≪≫
    (X.derivedIter N).dComplex.iCyclesIso i _ (dComplex_next i) hout

/-- An entry of the spectral sequence of a couple which has no incoming and no outgoing
differentials from the page `N₀` on is unchanged on the later pages. -/
noncomputable def derivedIterAddEIso (N₀ : ℕ) (i : κ)
    (hout : ∀ N, N₀ ≤ N → (X.derivedIter N).d i (i + (b + degIter a c N)) = 0)
    (hin : ∀ N, N₀ ≤ N → (X.derivedIter N).d (i - (b + degIter a c N)) i = 0) :
    (k : ℕ) → (X.derivedIter (N₀ + k)).E i ≅ (X.derivedIter N₀).E i
  | 0 => Iso.refl _
  | k + 1 => X.derivedIterSuccEIso (N₀ + k) i (hout _ (by omega)) (hin _ (by omega)) ≪≫
      derivedIterAddEIso N₀ i hout hin k

section Collapse

variable {b : ℤ × ℤ} (X : ExactCouple C ((-1, 0) : ℤ × ℤ) b 0)

/-- If the spectral sequence of a couple is concentrated in the column `p = 0` on some page,
then all the differentials vanish from that page on. -/
lemma d_eq_zero_of_isZero (hb : 0 < b.1) (N₀ : ℕ)
    (h : ∀ p n : ℤ, p ≠ 0 → IsZero ((X.derivedIter N₀).E (p, n))) (N : ℕ) (hN : N₀ ≤ N)
    (i j : ℤ × ℤ) : (X.derivedIter N).d i j = 0 := by
  by_cases hi : i.1 = 0
  · by_cases hj : i + (b + degIter ((-1, 0) : ℤ × ℤ) (0 : ℤ × ℤ) N) = j
    · apply IsZero.eq_of_tgt
      apply X.isZero_derivedIter_E N₀ N hN
      obtain ⟨p, n⟩ := j
      refine h p n ?_
      have := congrArg _root_.Prod.fst hj
      rw [degIter_neg_one_zero] at this
      simp at this
      omega
    · exact (X.derivedIter N).shape_d _ _ hj
  · apply IsZero.eq_of_src
    apply X.isZero_derivedIter_E N₀ N hN
    obtain ⟨p, n⟩ := i
    exact h p n hi


variable {X} {A : ℤ → C} {ι : ∀ p n : ℤ, X.D (p, n) ⟶ A n} {F : ∀ n, DecreasingFiltration (A n)}

/-- The *edge map* `Aⁿ ⟶ E_{N₀}^{0, n}` of a convergent couple, when `F⁰ Aⁿ = Aⁿ` and the
differentials vanish from the page `N₀` on: the projection `Aⁿ = F⁰ Aⁿ ⟶ gr⁰ Aⁿ`, followed by
the identification `gr⁰ Aⁿ ≅ E_∞^{0, n}` of the convergence data and `E_∞^{0, n} = E_{N₀}^{0, n}`.

(blueprint: `lem-sp-edge-collapse`) -/
noncomputable def ConvergenceData.edge (c : X.ConvergenceData ι F) (n : ℤ) (h₀ : (F n).F 0 = ⊤)
    (N₀ : ℕ) (hd : ∀ N, N₀ ≤ N → ∀ i j, (X.derivedIter N).d i j = 0) :
    A n ⟶ (X.derivedIter N₀).E (0, n) :=
  (Subobject.isoOfEqMk _ (𝟙 (A n)) (h₀.trans (Subobject.top_eq_id _))).inv ≫ cokernel.π _ ≫
    (c.iso 0 n (N₀ + (c.stage 0 n - N₀)) (by omega)).inv ≫
    (X.derivedIterAddEIso N₀ (0, n) (fun N hN ↦ hd N hN _ _) (fun N hN ↦ hd N hN _ _) _).hom

/-- **Edge collapse.** Let `X` be an exact couple (with `α` of degree `(-1, 0)`, `g` of degree
`0` and `f` of degree `b` with `b.1 > 0`) whose spectral sequence converges to finite
filtrations of objects `Aⁿ`, and suppose that on the page `N₀` all the entries `E^{p, n}` with
`p ≠ 0` vanish. Then all later differentials vanish (so that the later pages agree with that
page, see `CategoryTheory.ExactCouple.derivedIterAddEIso`), and the filtration of `Aⁿ` is
concentrated in degree `0`: `F⁰ Aⁿ = Aⁿ` and `F¹ Aⁿ = 0`. The edge map `Aⁿ ⟶ E_{N₀}^{0, n}` is
then an isomorphism (`CategoryTheory.ExactCouple.isIso_edge`).

(blueprint: `lem-sp-edge-collapse`) -/
theorem edge_collapse (hb : 0 < b.1) (c : X.ConvergenceData ι F)
    (hF : ∀ n, ∃ m M : ℤ, (F n).F m = ⊤ ∧ (F n).F M = ⊥) (N₀ : ℕ)
    (h : ∀ p n : ℤ, p ≠ 0 → IsZero ((X.derivedIter N₀).E (p, n))) :
    (∀ N, N₀ ≤ N → ∀ i j, (X.derivedIter N).d i j = 0) ∧
      ∀ n : ℤ, (F n).F 0 = ⊤ ∧ (F n).F 1 = ⊥ := by
  refine ⟨X.d_eq_zero_of_isZero hb N₀ h, fun n ↦ ?_⟩
  obtain ⟨m, M, hm, hM⟩ := hF n
  have hgr : ∀ p ≠ 0, IsZero ((F n).gr p) := fun p hp ↦
    (X.isZero_derivedIter_E N₀ _ (le_max_right _ _) _ (h p n hp)).of_iso
      (c.iso p n (max (c.stage p n) N₀) (le_max_left _ _)).symm
  exact ⟨(F n).F_eq_top_of_isZero_gr m 0 hm (fun k hk ↦ hgr k (by omega)),
    (F n).F_eq_bot_of_isZero_gr M 1 hM (fun k hk ↦ hgr k (by omega))⟩

/-- **The edge map is an isomorphism.** In the situation of
`CategoryTheory.ExactCouple.edge_collapse`, the edge map `Aⁿ ⟶ E_{N₀}^{0, n}` is an
isomorphism.

(blueprint: `lem-sp-edge-collapse`) -/
theorem isIso_edge (hb : 0 < b.1) (c : X.ConvergenceData ι F)
    (hF : ∀ n, ∃ m M : ℤ, (F n).F m = ⊤ ∧ (F n).F M = ⊥) (N₀ : ℕ)
    (h : ∀ p n : ℤ, p ≠ 0 → IsZero ((X.derivedIter N₀).E (p, n))) (n : ℤ) :
    IsIso (c.edge n ((edge_collapse hb c hF N₀ h).2 n).1 N₀ (edge_collapse hb c hF N₀ h).1) := by
  have h₁ := ((edge_collapse hb c hF N₀ h).2 n).2
  have : IsIso (cokernel.π (Subobject.ofLE _ _ ((F n).F_succ_le 0))) := by
    refine cokernel.π_of_zero (IsZero.eq_of_src ?_ _ _)
    exact (Subobject.botCoeIsoZero.isZero_iff.mpr (isZero_zero _)).of_iso
      (Subobject.isoOfEq _ _ (by simpa using h₁))
  dsimp only [ConvergenceData.edge]
  exact IsIso.comp_isIso' (Iso.isIso_inv _)
    (IsIso.comp_isIso' this (IsIso.comp_isIso' (Iso.isIso_inv _) (Iso.isIso_hom _)))


end Collapse

end ExactCouple

end CategoryTheory
