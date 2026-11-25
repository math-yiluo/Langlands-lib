/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # Degeneration of an exact couple supported on column zero

Source: Stacks Project, Tag 0H7Z, degeneration of its convergent spectral sequence.
(blueprint: lem-pur-column-zero-exact-couple)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem pullback_bot_eq_kernel {V W : C} (f : V ⟶ W) :
    (Subobject.pullback f).obj ⊥ = kernelSubobject f := by
  apply le_antisymm
  · apply le_kernelSubobject
    apply (Subobject.bot_factors_iff_zero _).mp
    apply (pullback_factors_iff f _ _).mp
    exact Subobject.factors_self _
  · apply Subobject.le_of_factors
    apply (pullback_factors_iff f _ _).mpr
    exact (Subobject.bot_factors_iff_zero _).mpr (kernelSubobject_arrow_comp f)

private theorem page_zero_off_column
    (X : BigradedExactCouple C 0)
    (hE : ∀ p q : ℤ, p ≠ 0 → IsZero (X.E p q)) :
    ∀ (r : ℕ) (p q : ℤ), p ≠ 0 → IsZero ((X.pageCouple r).E p q) := by
  intro r
  induction r with
  | zero => exact hE
  | succ r ih =>
    intro p q h
    change IsZero (cokernel _)
    apply IsZero.of_epi (cokernel.π _)
    exact IsZero.of_mono (kernel.ι ((X.pageCouple r).d p q)) (ih p q h)

private theorem differentials_zero
    (X : BigradedExactCouple C 0)
    (hE : ∀ p q : ℤ, p ≠ 0 → IsZero (X.E p q)) (r : ℕ) (p q : ℤ) :
    (X.pageCouple r).d p q = 0 ∧ (X.pageCouple r).dInto p q = 0 := by
  constructor
  · by_cases hp : p = 0
    · apply IsZero.eq_zero_of_tgt
      exact page_zero_off_column X hE r _ _ (by omega)
    · exact (page_zero_off_column X hE r p q hp).eq_zero_of_src _
  · by_cases hp : p = 0
    · apply IsZero.eq_zero_of_src
      exact page_zero_off_column X hE r _ _ (by omega)
    · exact (page_zero_off_column X hE r p q hp).eq_zero_of_tgt _

/-- With only column zero present all cycles are permanent and all boundaries vanish.
Source: Stacks Project, Tag 0H7Z. (blueprint: lem-pur-column-zero-exact-couple)
Proof: a later page is a subquotient of the initial page, so its other columns remain
zero. Every differential either has zero source or zero target. The cycle and boundary
recursions therefore leave the initial whole and zero subobjects unchanged. Take their
greatest lower and least upper bounds. -/
theorem column_zero_limit_subobjects
    (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (hE : ∀ p q : ℤ, p ≠ 0 → IsZero (X.E p q)) (p q : ℤ) :
    L.Z p q = ⊤ ∧ L.B p q = ⊥ := by
  have hs (r : ℕ) : X.cycleBoundaryTower.Z r p q = ⊤ ∧
      X.cycleBoundaryTower.B r p q = ⊥ := by
    induction r with
    | zero => exact ⟨X.cycleBoundaryTower.Z_zero p q, X.cycleBoundaryTower.B_zero p q⟩
    | succ r ih =>
      obtain ⟨ho, hi⟩ := differentials_zero X hE r p q
      constructor
      · rw [X.cycleBoundaryTower.Z_succ, ho, kernelSubobject_zero,
          Subobject.pullback_top, Subobject.exists_iso_map, Subobject.map_top,
          Subobject.mk_arrow, ih.1]
      · rw [X.cycleBoundaryTower.B_succ, hi, imageSubobject_zero,
          pullback_bot_eq_kernel, X.cycleBoundaryTower.projection_kernel,
          Subobject.exists_iso_map, Subobject.map_mk]
        simpa only [Subobject.ofLE_arrow, Subobject.mk_arrow] using ih.2
  constructor
  · apply top_unique
    apply (L.Z_glb p q).2
    rintro _ ⟨r, rfl⟩
    exact le_of_eq (hs r).1.symm
  · apply bot_unique
    apply (L.B_lub p q).2
    rintro _ ⟨r, rfl⟩
    exact le_of_eq (hs r).2

private theorem filtration_step_eq_of_zero_graded {A : C}
    (F : PBCDecreasingFiltration A) (p : ℤ) (hp : IsZero (F.gradedPiece p)) :
    F.step (p + 1) = F.step p := by
  let f := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  have : Epi f := Preadditive.epi_of_isZero_cokernel f hp
  have : IsIso f := isIso_of_mono_of_epi f
  exact Subobject.eq_of_comm (asIso f) (Subobject.ofLE_arrow _)

/-- For an exhaustive column-zero abutment filtration, its zeroth step is the whole object.
Source: Stacks Project, Tag 0H7Z. (blueprint: lem-pur-column-zero-exact-couple)
Proof: outside column zero, the limiting page and therefore the associated graded are zero.
For every negative p the inclusion F^(p+1) into F^p is thus an isomorphism. Integer induction
shows that every negative step equals F^0. Every positive step is contained in F^0 by
antitonicity. Exhaustivity then says F^0 is the whole object. -/
theorem column_zero_filtration_top
    (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hconv : ConvergesTo X L A)
    (hE : ∀ p q : ℤ, p ≠ 0 → IsZero (X.E p q)) (n : ℤ) :
    (X.imageFiltration n (A n)).step 0 = ⊤ := by
  let F := X.imageFiltration n (A n)
  have hgr (p : ℤ) (hp : p ≠ 0) : IsZero (F.gradedPiece p) := by
    have hz : IsZero (X.pageInfinity L p (n - p)) := by
      apply IsZero.of_epi (cokernel.π _)
      exact IsZero.of_mono (L.Z p (n - p)).arrow (hE p _ hp)
    have he := (weakConvergence_comparison X L A hconv.2.1.1 p (n - p)).choose
    have ht : p + (n - p) = n := by omega
    have hz' := IsZero.of_iso hz he.symm
    rw [ht] at hz'
    exact hz'
  have hstep (p : ℤ) (hp : p ≤ 0) : F.step p = F.step 0 := by
    have hh (k : ℕ) : F.step (-(k : ℤ)) = F.step 0 := by
      induction k with
      | zero => simp
      | succ k ih =>
        have ht := filtration_step_eq_of_zero_graded F (-((k + 1 : ℕ) : ℤ))
          (hgr _ (by omega))
        have he : -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) := by omega
        rw [he] at ht
        exact ht.symm.trans ih
    have he : p = -(Int.toNat (-p) : ℤ) := by omega
    rw [he]
    exact hh _
  apply hconv.2.1.2 n |>.2
  intro p
  obtain hp | hp := le_total p 0
  · rw [hstep p hp]
  · exact F.antitone_step hp

end CategoryTheory.BigradedExactCouple
