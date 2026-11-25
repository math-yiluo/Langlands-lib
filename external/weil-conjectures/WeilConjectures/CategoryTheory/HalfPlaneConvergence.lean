/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
import WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence

/-!
# Half-plane convergence of an exact couple

Source: blueprint node thm-sp-half-plane-convergence, order 511; Stacks Project,
Tags 011T and 012F (blueprint: thm-sp-half-plane-convergence).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem page_zero (X : BigradedExactCouple C 0) (a : ℤ)
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (r : ℕ) (p q : ℤ) (h : p < 0 ∨ q < a) :
    IsZero ((X.pageCouple r).E p q) := by
  induction r with
  | zero => exact hE p q h
  | succ r ih =>
    have : Epi ((X.pageCouple r).derivedEProjection p q) := by
      dsimp [derivedEProjection, derivedE]
      infer_instance
    exact IsZero.of_epi ((X.pageCouple r).derivedEProjection p q)
      (IsZero.of_mono (kernel.ι ((X.pageCouple r).d p q)) ih)

private theorem page_stable (X : BigradedExactCouple C 0) (a : ℤ)
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (r : ℕ) (p q : ℤ) (hr : (r : ℤ) + 2 > max (q - a + 1) p) :
    ∃ e : (X.pageCouple r).E p q ≅ (X.pageCouple (r + 1)).E p q,
      kernel.ι ((X.pageCouple r).d p q) ≫ e.hom =
        (X.pageCouple r).derivedEProjection p q := by
  have hout : (X.pageCouple r).d p q = 0 :=
    (page_zero X a hE r (p + 2 + r) (q - 1 - r)
      (Or.inr (by omega))).eq_zero_of_tgt _
  have hin : (X.pageCouple r).dInto p q = 0 :=
    (page_zero X a hE r (p - r - 2) (q + r + 1)
      (Or.inl (by omega))).eq_zero_of_src _
  have hlift : kernel.lift ((X.pageCouple r).d p q)
      ((X.pageCouple r).dInto p q) ((X.pageCouple r).dInto_comp_d p q) = 0 := by
    apply (cancel_mono (kernel.ι ((X.pageCouple r).d p q))).1
    simp [hin]
  have : IsIso (kernel.ι ((X.pageCouple r).d p q)) := by
    rw [hout]
    infer_instance
  have : IsIso ((X.pageCouple r).derivedEProjection p q) := by
    dsimp [derivedEProjection, derivedE]
    exact CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ _ (cokernel.condition _)) (cokernelIsCokernel _) hlift
  refine ⟨(asIso (kernel.ι ((X.pageCouple r).d p q))).symm ≪≫
    asIso ((X.pageCouple r).derivedEProjection p q), ?_⟩
  simp

private theorem couple_complete (X : BigradedExactCouple C 0) (a : ℤ)
    (hD : ∀ p q : ℤ, q < a → IsZero (X.D p q)) : X.IsComplete := by
  intro p q S hS
  let r : ℕ := (q - a + 1).toNat
  have hr : q - (r : ℤ) < a := by
    dsimp [r]
    omega
  have hz : X.incomingAlphaIter r p q = 0 :=
    (hD (p + r) (q - r) hr).eq_zero_of_src _
  apply le_antisymm _ bot_le
  simpa [hz, imageSubobject_zero] using hS r

private theorem pullback_bot_kernel {T U : C} (f : T ⟶ U) :
    (Subobject.pullback f).obj ⊥ = kernelSubobject f := by
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply kernelSubobject_factors
    have hw := (Subobject.isPullback f (⊥ : Subobject U)).w
    simpa using hw.symm
  · apply Subobject.le_of_factors
    apply pullback_factors
    rw [kernelSubobject_arrow_comp]
    exact Subobject.factors_zero

private theorem tower_stationary (X : BigradedExactCouple C 0) (r : ℕ) (p q : ℤ)
    (hout : (X.pageCouple r).d p q = 0)
    (hin : (X.pageCouple r).dInto p q = 0) :
    X.cycleBoundaryTower.Z (r + 1) p q = X.cycleBoundaryTower.Z r p q ∧
      X.cycleBoundaryTower.B (r + 1) p q = X.cycleBoundaryTower.B r p q := by
  constructor
  · rw [X.cycleBoundaryTower.Z_succ, hout, kernelSubobject_zero,
      Subobject.pullback_top, Subobject.exists_iso_map, Subobject.map_top,
      Subobject.mk_arrow]
  · rw [X.cycleBoundaryTower.B_succ, hin, imageSubobject_zero,
      pullback_bot_kernel, X.cycleBoundaryTower.projection_kernel,
      Subobject.exists_iso_map, Subobject.map_mk]
    simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]

private theorem half_plane_limits (X : BigradedExactCouple C 0) (a : ℤ)
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q)) :
    X.IsRegular ∧ Nonempty (LimitSubobjects X) := by
  let R : ℤ → ℤ → ℕ := fun p q ↦ (max (q - a + 1) p + 1).toNat
  have hR (p q : ℤ) : (R p q : ℤ) + 2 > max (q - a + 1) p := by
    dsimp [R]
    omega
  have hstationary (p q : ℤ) (t : ℕ) (ht : R p q ≤ t) :
      X.cycleBoundaryTower.Z (t + 1) p q = X.cycleBoundaryTower.Z t p q ∧
        X.cycleBoundaryTower.B (t + 1) p q = X.cycleBoundaryTower.B t p q := by
    have hr := hR p q
    apply tower_stationary
    · exact (page_zero X a hE t (p + 2 + t) (q - 1 - t)
        (Or.inr (by omega))).eq_zero_of_tgt _
    · exact (page_zero X a hE t (p - t - 2) (q + t + 1)
        (Or.inl (by omega))).eq_zero_of_src _
  have htail (p q : ℤ) (k : ℕ) :
      X.cycleBoundaryTower.Z (R p q + k) p q = X.cycleBoundaryTower.Z (R p q) p q ∧
        X.cycleBoundaryTower.B (R p q + k) p q = X.cycleBoundaryTower.B (R p q) p q := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := hstationary p q (R p q + k) (by omega)
      simpa only [Nat.add_succ] using ⟨hs.1.trans ih.1, hs.2.trans ih.2⟩
  have heventual (p q : ℤ) (t : ℕ) (ht : R p q ≤ t) :
      X.cycleBoundaryTower.Z t p q = X.cycleBoundaryTower.Z (R p q) p q ∧
        X.cycleBoundaryTower.B t p q = X.cycleBoundaryTower.B (R p q) p q := by
    simpa only [Nat.add_sub_of_le ht] using htail p q (t - R p q)
  refine ⟨fun p q ↦ ⟨R p q, fun t ht ↦ (heventual p q t ht).2⟩, ?_⟩
  refine ⟨{ Z := fun p q ↦ X.cycleBoundaryTower.Z (R p q) p q
            B := fun p q ↦ X.cycleBoundaryTower.B (R p q) p q
            Z_glb := ?_
            B_lub := ?_ }⟩
  · intro p q
    have hmono := antitone_nat_of_succ_le (f := fun r ↦ X.cycleBoundaryTower.Z r p q)
      (fun r ↦ X.cycleBoundaryTower.Z_decreasing r p q)
    refine ⟨?_, fun S hS ↦ hS ⟨R p q, rfl⟩⟩
    rintro S ⟨t, rfl⟩
    by_cases ht : R p q ≤ t
    · exact le_of_eq (heventual p q t ht).1.symm
    · exact hmono (by omega)
  · intro p q
    have hmono := monotone_nat_of_le_succ (f := fun r ↦ X.cycleBoundaryTower.B r p q)
      (fun r ↦ X.cycleBoundaryTower.B_increasing r p q)
    refine ⟨?_, fun S hS ↦ hS ⟨R p q, rfl⟩⟩
    rintro S ⟨t, rfl⟩
    by_cases ht : R p q ≤ t
    · exact le_of_eq (heventual p q t ht).2
    · exact hmono (by omega)

private theorem finite_inverse_limit {T : C} (F : PBCDecreasingFiltration T)
    (m : ℤ) (hm : F.step m = ⊥) : IsInverseLimit F := by
  have hz (p : ℤ) (hp : m ≤ p) : F.step p = ⊥ :=
    le_antisymm (hm ▸ F.antitone_step hp) bot_le
  have hπ (p : ℤ) (hp : m ≤ p) : IsIso (cokernel.π (F.step p).arrow) := by
    apply CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ _ (cokernel.condition _)) (cokernelIsCokernel _)
    apply Subobject.mk_eq_bot_iff_zero.mp
    simpa only [Subobject.mk_arrow] using hz p hp
  have hcomm (p : ℤ) :
      cokernel.π (F.step (p + 1)).arrow ≫ quotientTransition F p =
        cokernel.π (F.step p).arrow := by
    exact cokernel.π_desc _ _ _
  intro S f hf
  have := hπ m le_rfl
  let h : S ⟶ T := f m ≫ inv (cokernel.π (F.step m).arrow)
  have hbase : h ≫ cokernel.π (F.step m).arrow = f m := by simp [h]
  refine ⟨h, ?_, ?_⟩
  · intro p
    induction p using Int.inductionOn' with
    | b => exact m
    | zero => exact hbase
    | succ p hp ih =>
      have := hπ p hp
      have := hπ (p + 1) (by omega)
      have : IsIso (quotientTransition F p) := by
        have heq : quotientTransition F p =
            inv (cokernel.π (F.step (p + 1)).arrow) ≫ cokernel.π (F.step p).arrow := by
          apply (cancel_epi (cokernel.π (F.step (p + 1)).arrow)).1
          simp [hcomm]
        rw [heq]
        infer_instance
      apply (cancel_mono (quotientTransition F p)).1
      rw [Category.assoc, hcomm, hf, ih]
    | pred p hp ih =>
      have ih' : h ≫ cokernel.π (F.step (p - 1 + 1)).arrow = f (p - 1 + 1) := by
        exact Eq.mp (congrArg (fun j : ℤ ↦ h ≫ cokernel.π (F.step j).arrow = f j)
          (show p = p - 1 + 1 by omega)) ih
      calc
        h ≫ cokernel.π (F.step (p - 1)).arrow =
            h ≫ (cokernel.π (F.step (p - 1 + 1)).arrow ≫
              quotientTransition F (p - 1)) := by rw [hcomm]
        _ = f (p - 1 + 1) ≫ quotientTransition F (p - 1) := by
          rw [← Category.assoc, ih']
        _ = f (p - 1) := hf (p - 1)
  · intro h' hh'
    apply (cancel_mono (cokernel.π (F.step m).arrow)).1
    exact (hh' m).trans hbase.symm

/-- Half-plane exact couples stabilize and converge to the finite image filtration.
Here `pageCouple r` is the actual page `r + 2`, so the stabilization bound below
is `(r : ℤ) + 2 > max (q - a + 1) p`.

Proof, Step 1: The half-plane region implies `a ≤ q ≤ n` on total degree `n`.
The incoming differential has source first index `p - R < 0` for `R > p`,
and the outgoing differential has target second index `q - R + 1 < a` for
`R > q - a + 1`. Page cohomology therefore gives the canonical stabilization
isomorphism, and the recursive cycles and boundaries become constant, yielding
regularity and limiting subobjects (def-sp-exact-couple, def-sp-convergence).
The incoming image of `alpha^R` is zero for `R > q - a`, yielding completeness.
Exactness makes alpha an isomorphism to the left of first index zero, since both
adjacent initial E terms vanish there. Thus the diagonal colimit is `D 0 n`,
with its map from first index zero the identity. Its image filtration is zero
for `q < a` and the whole object for `q ≥ n`.

Step 2: For `p ≥ 0`, choose a stabilized page `R` with `u = p - R + 2 ≤ 0`
and `v = q + R - 2`. By lem-sp-derived-couple-exact, the iterated D image
at `(u,v)` identifies with `G_q`, and its incoming alpha image with `G_(q-1)`.
The next D term is zero because its incoming source has second index below a.
Exactness gives `E_R = G_q / G_(q-1)`, hence the graded piece of `F` in
sense of def-sp-filtration. Iterating the defining equation for derived g shows
that the two canonical maps from `D p q` are onto with equal kernels; thus
this is the canonical comparison of def-sp-convergence. For `p < 0`, both
sides are zero. The finite filtration is exhaustive, separated and complete
in the inverse-limit sense, proving convergence.

Step 3: Compare the cycle/boundary formulas in Stacks Tag 011T and the
infinite-page and associated-graded discussion in Tag 012F.
Source: blueprint node thm-sp-half-plane-convergence, order 511; Stacks Project,
Tags 011T and 012F (blueprint: thm-sp-half-plane-convergence). -/
theorem halfPlaneConvergence
    (X : BigradedExactCouple C 0) (a : ℤ)
    (hD : ∀ (p q : ℤ), q < a → IsZero (X.D p q))
    (hE : ∀ (p q : ℤ), (p < 0 ∨ q < a) → IsZero (X.E p q)) :
    ∃ L : LimitSubobjects X, ∃ A : ∀ n : ℤ, AlphaColimit X n,
      ∃ hA : ∀ n : ℤ, (A n).obj = X.D 0 n,
      (∀ n : ℤ, (A n).ι 0 ≫ eqToHom (hA n) =
        eqToHom (by congr 1; omega)) ∧
      (∀ (r : ℕ) (n p q : ℤ), p + q = n →
        ¬ IsZero ((X.pageCouple r).E p q) → a ≤ q ∧ q ≤ n) ∧
      (∀ (r : ℕ) (p q : ℤ),
        (r : ℤ) + 2 > max (q - a + 1) p →
          ∃ e : (X.pageCouple r).E p q ≅ (X.pageCouple (r + 1)).E p q,
            kernel.ι ((X.pageCouple r).d p q) ≫ e.hom =
              (X.pageCouple r).derivedEProjection p q) ∧
      (∀ (n p : ℤ), p ≤ 0 → (X.imageFiltration n (A n)).step p = ⊤) ∧
      (∀ n : ℤ, (X.imageFiltration n (A n)).IsFinite ∧
        (X.imageFiltration n (A n)).IsExhaustive ∧
        (X.imageFiltration n (A n)).IsSeparated) ∧
      (∀ (p q : ℤ),
        ∃ e : X.pageInfinity L p q ≅
          (X.imageFiltration (p + q) (A (p + q))).gradedPiece p,
          X.toPageInfinity L p q ≫ e.hom = X.toGradedPiece A p q) ∧
      X.IsComplete ∧ X.ConvergesTo L A := by
  obtain ⟨hregular, ⟨L⟩⟩ := half_plane_limits X a hE
  obtain ⟨A, hA, hι, hiso⟩ := halfPlane_diagonal_colimits X
    (fun p q hp ↦ hE p q (Or.inl hp))
  have htop (n p : ℤ) (hp : p ≤ 0) : (X.imageFiltration n (A n)).step p = ⊤ := by
    have := hiso n p hp
    dsimp [imageFiltration]
    rw [imageSubobject_mono]
    exact Subobject.mk_eq_top_of_isIso _
  have hbot (n p : ℤ) (hp : n - a < p) : (X.imageFiltration n (A n)).step p = ⊥ := by
    have hz : (A n).ι p = 0 := (hD p (n - p) (by omega)).eq_zero_of_src _
    dsimp [imageFiltration]
    simp only [hz, imageSubobject_zero]
  have hfinite (n : ℤ) : (X.imageFiltration n (A n)).IsFinite :=
    ⟨0, n - a + 1, htop n 0 le_rfl, hbot n (n - a + 1) (by omega)⟩
  have hexhaustive (n : ℤ) : (X.imageFiltration n (A n)).IsExhaustive := by
    intro S hS
    exact top_unique (htop n 0 le_rfl ▸ hS 0)
  have hseparated (n : ℤ) : (X.imageFiltration n (A n)).IsSeparated := by
    intro S hS
    exact bot_unique (hbot n (n - a + 1) (by omega) ▸ hS (n - a + 1))
  have hweak := halfPlane_weak_convergence X a hD hE L A hA hι
  refine ⟨L, A, hA, hι, ?_, page_stable X a hE, htop, ?_, ?_,
    couple_complete X a hD, ?_⟩
  · intro r n p q hn hne
    have hq : a ≤ q := le_of_not_gt (fun h ↦ hne (page_zero X a hE r p q (Or.inr h)))
    have hp : 0 ≤ p := le_of_not_gt (fun h ↦ hne (page_zero X a hE r p q (Or.inl h)))
    exact ⟨hq, by omega⟩
  · exact fun n ↦ ⟨hfinite n, hexhaustive n, hseparated n⟩
  · intro p q
    obtain ⟨e, he, _⟩ := X.weakConvergence_comparison L A hweak p q
    exact ⟨e, he⟩
  · exact ⟨hregular, ⟨hweak, fun n ↦ ⟨hseparated n, hexhaustive n⟩⟩,
      fun n ↦ finite_inverse_limit _ (n - a + 1) (hbot n (n - a + 1) (by omega))⟩

end CategoryTheory.BigradedExactCouple
