/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic

/-! # Collapse of a first-quadrant spectral sequence supported in row zero

Source: Stacks Project, Tags 011O and 0132.
(blueprint: lem-sc-spectral-sequence-nat-row-zero)
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

/-- A first-quadrant spectral sequence with zero positive rows on page two computes
its abutment from the bottom row of page two.

Source: Stacks Project, Tags 011O and 0132.
(blueprint: lem-sc-spectral-sequence-nat-row-zero)

Proof: Vanishing of the positive rows propagates by taking homology. Every
bottom-row differential is zero: the outgoing differential has no target in the
first quadrant and the incoming differential has source in a positive row.
Thus the bottom row is stationary. In total degree n, all filtration quotients
before the nth are zero, so successive inclusions are isomorphisms and the nth
step is the whole abutment. Its next step is zero, so its quotient is itself.
The convergence identification and the stationary-page identification give the
claimed isomorphism. This argument also applies in degree zero. -/
theorem SpectralSequence.nonempty_abutment_iso_row_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : E₂CohomologicalSpectralSequenceNat C) (H : ℕ → C)
    (hH : E.AbutsTo H)
    (hrow : ∀ p q : ℕ, 0 < q → IsZero ((E.page 2).X (p, q))) (n : ℕ) :
    Nonempty (H n ≅ (E.page 2).X (n, 0)) := by
  have hpages (k p q : ℕ) (hq : 0 < q) :
      IsZero ((E.page (k + 2 : ℕ)).X (p, q)) := by
    induction k with
    | zero => simpa using hrow p q hq
    | succ k ih =>
      exact (E.iso (k + 2 : ℕ) (k + 1 + 2 : ℕ) (p, q) (by omega)
        (by omega)).isZero_iff.mp
          (((E.page (k + 2 : ℕ)).sc (p, q)).isZero_homology_of_isZero_X₂ ih)
  have hstation (k : ℕ) :
      Nonempty ((E.page 2).X (n, 0) ≅ (E.page (k + 2 : ℕ)).X (n, 0)) := by
    induction k with
    | zero => exact ⟨Iso.refl _⟩
    | succ k ih =>
      obtain ⟨e⟩ := ih
      let K := E.page (k + 2 : ℕ)
      let c := ComplexShape.spectralSequenceNat (⟨(k + 2 : ℕ), 1 - ((k + 2 : ℕ) : ℤ)⟩ : ℤ × ℤ)
      have hout : K.d (n, 0) (c.next (n, 0)) = 0 := by
        apply K.shape
        simp only [ComplexShape.spectralSequenceNat_rel_iff]
        omega
      have hin : K.d (c.prev (n, 0)) (n, 0) = 0 := by
        by_cases h : c.Rel (c.prev (n, 0)) (n, 0)
        · have hq : 0 < (c.prev (n, 0)).2 := by
            dsimp only [c] at h ⊢
            simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
            omega
          exact (hpages k _ _ hq).eq_of_src _ _
        · exact K.shape _ _ h
      exact ⟨e ≪≫ (K.iCyclesIso (n, 0) _ rfl hout).symm ≪≫
        K.isoHomologyπ _ (n, 0) rfl hin ≪≫
        E.iso (k + 2 : ℕ) (k + 1 + 2 : ℕ) (n, 0) (by omega) (by omega)⟩
  obtain ⟨A⟩ := hH
  have htop (p : ℕ) (hp : p ≤ n) : A.filtration n p = ⊤ := by
    induction p with
    | zero => exact A.filtration_zero n
    | succ p ih =>
      have heq : A.filtration n (p + 1) = A.filtration n p := by
        let f := Subobject.ofLE _ _ (A.filtration_succ_le n p)
        obtain ⟨e⟩ := A.nonempty_gradedIso n p (n - p) (by omega)
        have hz : IsZero (E.pageInfinity (p, n - p)) := by
          dsimp [SpectralSequence.pageInfinity]
          exact (E.pageXIsoOfEq (p, n - p) _ (n + 2 : ℕ)
            (by omega) (by omega)).isZero_iff.mpr (hpages n p (n - p) (by omega))
        have : Epi f := Preadditive.epi_of_isZero_cokernel f (e.isZero_iff.mpr hz)
        have : IsIso f := isIso_of_mono_of_epi f
        exact Subobject.eq_of_comm (asIso f) (Subobject.ofLE_arrow _)
      rw [heq, ih (by omega)]
  let f := Subobject.ofLE _ _ (A.filtration_succ_le n n)
  have hf : f = 0 := by
    apply (cancel_mono (A.filtration n n).arrow).mp
    simp only [f, Subobject.ofLE_arrow, zero_comp]
    exact (Subobject.mk_eq_bot_iff_zero (f := (A.filtration n (n + 1)).arrow)).mp
      (by simpa only [Subobject.mk_arrow] using A.filtration_succ_self n)
  have : IsIso (cokernel.π f) := cokernel.π_of_zero hf
  have : IsIso (A.filtration n n).arrow := by rw [htop n le_rfl]; infer_instance
  obtain ⟨e⟩ := A.nonempty_gradedIso n n 0 (by omega)
  obtain ⟨s⟩ := hstation n
  exact ⟨(asIso (A.filtration n n).arrow).symm ≪≫ asIso (cokernel.π f) ≪≫ e ≪≫ s.symm⟩

end CategoryTheory
