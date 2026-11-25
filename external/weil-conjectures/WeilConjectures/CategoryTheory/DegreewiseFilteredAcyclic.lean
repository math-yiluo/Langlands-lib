/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.FilteredComplexSpectralSequence
import WeilConjectures.CategoryTheory.DegreewiseFilteredStableQuotient

/-! # Acyclicity from a degreewise finite filtration

Source: Stacks Project, Homology, Tag 012W, Lemma `lemma-biregular-ss-converges`.
(blueprint: lem-sp-degreewise-filtered-acyclic).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem isZero_of_finite_filtration
    {C : Type u} [Category.{v} C] [Abelian C] {X : C}
    (F : DecreasingFiltration X) (hfinite : F.IsFinite)
    (hgraded : ∀ p : ℤ, IsZero (F.gradedPiece p)) : IsZero X := by
  have hstep (p : ℤ) : F.step (p + 1) = F.step p := by
    let i := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
    have : Epi i := Preadditive.epi_of_isZero_cokernel i (hgraded p)
    have : IsIso i := isIso_of_mono_of_epi i
    exact Subobject.eq_of_comm (asIso i) (Subobject.ofLE_arrow _)
  have hconstant (p : ℤ) (k : ℕ) : F.step (p + k) = F.step p := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show p + (k + 1 : ℕ) = (p + k) + 1 by omega, hstep, ih]
  obtain ⟨lo, hi, hlo, hhi⟩ := hfinite
  change F.step lo = ⊤ at hlo
  change F.step hi = ⊥ at hhi
  have hEq : (⊤ : Subobject X) = ⊥ := by
    by_cases h : lo ≤ hi
    · have he := hconstant lo (hi - lo).toNat
      rw [show lo + ((hi - lo).toNat : ℤ) = hi by omega, hhi, hlo] at he
      exact he.symm
    · have he := hconstant hi (lo - hi).toNat
      rw [show hi + ((lo - hi).toNat : ℤ) = lo by omega, hlo, hhi] at he
      exact he
  apply (IsZero.iff_id_eq_zero X).mpr
  apply Subobject.mk_eq_bot_iff_zero.mp
  simpa only [Subobject.top_eq_id] using hEq

private theorem page_zero_of_first
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0) (pq : ℤ × ℤ)
    (h : IsZero ((E.page 1).X pq)) (r : ℤ) (hr : 1 ≤ r) :
    IsZero ((E.page r (by omega)).X pq) := by
  have hn : ∀ k : ℕ, IsZero ((E.page (1 + k) (by omega)).X pq) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      exact (E.iso (1 + k) (1 + (k + 1)) pq (by omega) (by omega)).isZero_iff.mp
        ((E.page (1 + k) (by omega)).sc pq |>.isZero_homology_of_isZero_X₂ ih)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, r = 1 + k := ⟨(r - 1).toNat, by omega⟩
  subst r
  exact hn k

/-- A cochain complex with a degreewise finite subcomplex filtration and acyclic
associated graded complexes is acyclic.
Source: Stacks Project, Homology, Tag 012W, Lemma `lemma-biregular-ss-converges`,
parts (2)--(4), applied to the zero Serre subcategory.
(blueprint: lem-sp-degreewise-filtered-acyclic).

Proof.
1. Construct the filtered-complex spectral sequence. The differential-compatible
page-zero identifications identify its short complexes with those of the graded
complexes. Their acyclicity makes page one zero. The successor-page homology
isomorphisms make every positive page zero by induction.
2. Degreewise finite convergence identifies a sufficiently late cycle/boundary
quotient at (p,n-p) with the p-th graded piece of the finite image filtration on
H^n(K). Its page comparison therefore makes that graded piece zero.
3. Zero successive cokernels make successive filtration inclusions epimorphisms;
they are already monomorphisms, hence isomorphisms. The corresponding subobjects
are equal. A finite induction between the top and bottom bounds gives top = bottom,
so H^n(K) is zero. This works in every degree, proving acyclicity. -/
theorem degreewiseFiltered_acyclic
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (hfinite : ∀ n : ℤ, ∃ lo hi : ℤ,
      F.complexStep lo n = ⊤ ∧ F.complexStep hi n = ⊥)
    (hgraded : ∀ p : ℤ, (F.gradedPiece p).Acyclic) : K.Acyclic := by
  obtain ⟨E, e, hd, hquot⟩ := filteredComplex_associated_spectralSequence K F
  have hfirst (p q : ℤ) : IsZero ((E.page 1).X (p, q)) := by
    let P := E.page 0
    let G := F.gradedPiece p
    have hprev : (ComplexShape.up' (⟨0, 1⟩ : ℤ × ℤ)).prev (p, q) = (p, q - 1) := by
      apply ComplexShape.prev_eq'
      change (p, q - 1) + (0, 1) = (p, q)
      ext <;> dsimp <;> omega
    have hnext : (ComplexShape.up' (⟨0, 1⟩ : ℤ × ℤ)).next (p, q) = (p, q + 1) := by
      apply ComplexShape.next_eq'
      change (p, q) + (0, 1) = (p, q + 1)
      ext <;> simp
    have hi : P.sc' (p, q - 1) (p, q) (p, q + 1) ≅
        G.sc' (p + (q - 1)) (p + q) (p + (q + 1)) := by
      refine ShortComplex.isoMk (e p (q - 1)) (e p q) (e p (q + 1)) ?_ ?_
      · have hd' := hd p (q - 1)
        rw [show q - 1 + 1 = q by omega] at hd'
        exact hd'.symm
      · exact (hd p q).symm
    have hg : (G.sc' (p + (q - 1)) (p + q) (p + (q + 1))).Exact :=
      (G.exactAt_iff' (p + (q - 1)) (p + q) (p + (q + 1))
        (by simp; omega) (by simp; omega)).mp (hgraded p (p + q))
    have hp : P.ExactAt (p, q) :=
      (P.exactAt_iff' _ _ _ hprev hnext).mpr (ShortComplex.exact_of_iso hi.symm hg)
    exact (E.iso 0 1 (p, q) rfl (by omega)).isZero_iff.mp hp.isZero_homology
  obtain ⟨H, hHfinite, _, hstable⟩ := degreewiseFiltered_stable_quotient K F hfinite
    (fun n ↦ K.homology n) (fun _ ↦ Iso.refl _)
  intro n
  apply (K.exactAt_iff_isZero_homology n).mpr
  apply isZero_of_finite_filtration (H n) (hHfinite n)
  intro p
  obtain ⟨t, ht, htail⟩ := hstable p n
  obtain ⟨hBZ, ⟨f⟩⟩ := htail t le_rfl
  have hquotn := hquot p (n - p) t ht
  rw [show p + (n - p) = n by omega] at hquotn
  obtain ⟨hBZ', ⟨g⟩⟩ := hquotn
  have hzero := page_zero_of_first E (p, n - p) (hfirst p (n - p)) t ht
  have hz : IsZero (cokernel (Subobject.ofLE _ _ hBZ)) := by
    exact g.isZero_iff.mp hzero
  exact f.isZero_iff.mp hz

end CategoryTheory
