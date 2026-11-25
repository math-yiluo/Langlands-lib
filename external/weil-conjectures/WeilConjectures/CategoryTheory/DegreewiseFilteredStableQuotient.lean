/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.FilteredStableSubquotient
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # Stationary quotients for a degreewise finite filtered complex

Source: Stacks Project, Tags 012Q, 012W and 0132.
(blueprint: lem-sp-degreewise-filtered-stable-quotient).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem gradedPiece_quotient_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A Y : C} (F : DecreasingFiltration A) (c : A ≅ Y) (p : ℤ) :
    Nonempty (F.gradedPiece p ≅ (F.quotient c.hom).gradedPiece p) := by
  let G := F.quotient c.hom
  have heq (i : ℤ) : G.step i = Subobject.mk ((F.step i).arrow ≫ c.hom) := by
    change imageSubobject ((F.step i).arrow ≫ c.hom) = _
    exact imageSubobject_mono _
  let e (i : ℤ) : (G.step i : C) ≅ (F.step i : C) :=
    Subobject.isoOfEqMk _ _ (heq i)
  have comm : Subobject.ofLE (G.step (p + 1)) (G.step p)
      (G.antitone_step (by omega)) ≫ (e p).hom =
      (e (p + 1)).hom ≫ Subobject.ofLE (F.step (p + 1)) (F.step p)
        (F.antitone_step (by omega)) := by
    apply (cancel_mono ((F.step p).arrow ≫ c.hom)).1
    simp [e, Category.assoc]
  exact ⟨(cokernel.mapIso _ _ (e (p + 1)) (e p) comm).symm⟩

private theorem stableBoundaries_le_cycles
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n r : ℤ)
    (hupper : L.complexStep (p + r) (n + 1) = ⊥)
    (hlower : L.complexStep (p - r + 1) (n - 1) = ⊤) :
    L.complexBoundaries p n r ≤ L.complexCycles p n r := by
  have h : imageSubobject (K.d (n - 1) n) ≤
      (Subobject.pullback (K.d n (n + 1))).obj ⊥ := by
    apply (Subobject.imageSubobject_le_iff _ _).2
    apply (Subobject.factors_pullback_obj_iff _ _ _).2
    apply (Subobject.bot_factors_iff_zero _).2
    exact K.d_comp_d _ _ _
  dsimp only [DecreasingFiltration.complexBoundaries, DecreasingFiltration.complexCycles]
  rw [hlower, hupper, Subobject.exists_obj_top]
  apply Functor.monotone
  apply Functor.monotone
  exact sup_le_sup_right (inf_le_inf_left _ h) _

set_option linter.unusedVariables false in
/-- The stationary cycle/boundary quotient is the graded image filtration on cohomology.
Only degreewise finiteness is needed; no spectral sequence is part of this statement.
Source: Stacks Project, Tags 012Q (stable subquotients),
012W (degreewise finite convergence) and 0132.
(blueprint: lem-sp-degreewise-filtered-stable-quotient).

Proof.
For each n define the p-th step on H^n(K) to be the image of H^n(L^pK) → H^n(K).
The factorization through L^pK of the inclusion of L^qK for p ≤ q gives
antitonicity. Pick bounds for degrees n-1,n,n+1. For p below all their lower
bounds the subcomplex inclusion is an isomorphism in these three degrees, so
its homology image is top. Above the upper bound in degree n its homology
image is zero. Thus the image filtration is finite.
Fix p,n. Choose t ≥ 1 so that L^(p+t)K^(n+1)=0 and
L^(p-t+1)K^(n-1)=K^(n-1). Antitonicity keeps these equalities true for every
r ≥ t. In the formulas for Z_r and B_r the outer steps can therefore be
replaced by zero and the whole object. The cycles are the images in gr^pK^n
of actual cycles in L^pK^n, while the boundaries are the images of actual
boundaries of K intersected with L^pK^n. The abelian subquotient isomorphism
identifies Z_r/B_r with the quotient of the image of H^n(L^pK) by the image
of H^n(L^(p+1)K). This is the graded piece of the image filtration.
For a family c_n:H^n(K) ≅ Y^n, take direct images of these steps along c_n.hom.
Their antitonicity is preserved by the direct-image functor. Since each c_n
is an isomorphism, direct image preserves top and bottom and identifies the
successive inclusion arrows up to isomorphism. Applying the cokernel functor
to these squares gives the graded-piece comparisons. This yields the exact
step formula, finiteness and stationary-quotient isomorphisms below. -/
theorem degreewiseFiltered_stable_quotient
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (L : DecreasingFiltration K)
    (hfinite : ∀ n : ℤ, ∃ lo hi : ℤ,
      L.complexStep lo n = ⊤ ∧ L.complexStep hi n = ⊥)
    (Y : ℤ → C) (c : ∀ n : ℤ, K.homology n ≅ Y n) :
    ∃ H : ∀ n : ℤ, DecreasingFiltration (Y n),
      (∀ n : ℤ, (H n).IsFinite) ∧
      (∀ p n : ℤ, (H n).step p =
        (Subobject.«exists» (c n).hom).obj
          (imageSubobject (HomologicalComplex.homologyMap (L.step p).arrow n))) ∧
      (∀ p n : ℤ, ∃ (t : ℤ) (ht : 1 ≤ t), ∀ (r : ℤ) (hr : t ≤ r),
        ∃ hBZ : L.complexBoundaries p n r ≤ L.complexCycles p n r,
          Nonempty (cokernel (Subobject.ofLE _ _ hBZ) ≅ (H n).gradedPiece p)) := by
  let H : ∀ n : ℤ, DecreasingFiltration (Y n) :=
    fun n ↦ (L.homologyFiltration n).quotient (c n).hom
  refine ⟨H, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨lo, hi, hlo, hhi⟩ := L.cohomologyImage_isFinite hfinite n
    change (L.homologyFiltration n).step lo = ⊤ at hlo
    change (L.homologyFiltration n).step hi = ⊥ at hhi
    refine ⟨lo, hi, ?_, ?_⟩
    · change imageSubobject (((L.homologyFiltration n).step lo).arrow ≫ (c n).hom) = ⊤
      rw [← Subobject.exists_obj_eq_imageSubobject, hlo,
        Subobject.exists_iso_map, Subobject.map_top]
      exact Subobject.mk_eq_top_of_isIso _
    · change imageSubobject (((L.homologyFiltration n).step hi).arrow ≫ (c n).hom) = ⊥
      rw [← Subobject.exists_obj_eq_imageSubobject, hhi,
        Subobject.exists_iso_map, Subobject.map_bot]
  · intro p n
    exact (Subobject.exists_obj_eq_imageSubobject (c n).hom
      ((L.homologyFiltration n).step p)).symm
  · intro p n
    obtain ⟨lo, _, hlo, _⟩ := hfinite (n - 1)
    obtain ⟨_, hi, _, hhi⟩ := hfinite (n + 1)
    let t := max 1 (max (hi - p) (p + 1 - lo))
    have ht : 1 ≤ t := le_max_left _ _
    refine ⟨t, ht, ?_⟩
    intro r hr
    have mono (i : ℤ) : Antitone (fun q ↦ L.complexStep q i) := by
      intro a b hab
      have h := imageSubobject_comp_le
        ((Subobject.ofLE (L.step b) (L.step a) (L.antitone_step hab)).f i)
        ((L.step a).arrow.f i)
      simpa only [DecreasingFiltration.complexStep, ← HomologicalComplex.comp_f,
        Subobject.ofLE_arrow] using h
    have hu : L.complexStep (p + r) (n + 1) = ⊥ := by
      apply bot_unique
      rw [← hhi]
      apply mono
      have : hi - p ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
      omega
    have hl : L.complexStep (p - r + 1) (n - 1) = ⊤ := by
      apply top_unique
      rw [← hlo]
      apply mono
      have : p + 1 - lo ≤ t := le_trans (le_max_right _ _) (le_max_right _ _)
      omega
    have hBZ := stableBoundaries_le_cycles L p n r hu hl
    obtain ⟨e⟩ := L.stableSubquotient_at_bounds p n r (le_trans ht hr) hu hl hBZ
    obtain ⟨e'⟩ := gradedPiece_quotient_iso (L.homologyFiltration n) (c n) p
    exact ⟨hBZ, ⟨e ≪≫ e'⟩⟩

end CategoryTheory
