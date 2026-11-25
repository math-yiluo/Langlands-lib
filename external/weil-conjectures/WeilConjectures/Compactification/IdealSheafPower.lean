/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.FiniteTypeExtension

/-!
# Powers of a finite-type ideal sheaf inside an ideal sheaf

If `A` and `B` are quasi-coherent ideal sheaves on a quasi-compact scheme with `B` of
finite type and `V(A) ⊆ V(B)`, then some power of `B` is contained in `A`
(blueprint: `lemma:nagata-finite-type-ideal-power-in-ideal`).

The containment `V(A) ⊆ V(B)` says exactly that `B` is contained in the radical of `A`, so
on every affine open the ideal of sections of `B` is a finitely generated ideal inside the
radical of the ideal of sections of `A`; `Ideal.exists_pow_le_of_le_radical_of_fg` then
produces an exponent there. Quasi-compactness bounds these exponents: the maximum over a
finite affine cover works globally, since containment of ideal sheaves can be checked on
an affine cover (`Scheme.IdealSheafData.le_of_iSup_eq_top`).

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_le`: on a quasi-compact scheme, a
  finite-type ideal sheaf whose support contains the support of another ideal sheaf has a
  power contained in that ideal sheaf.

-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **A finite-type ideal sheaf has a power inside any ideal sheaf whose support it
contains.** If `X` is quasi-compact, `B` is of finite type and `V(A) ⊆ V(B)`, then
`B ^ n ≤ A` for some `n`. -/
theorem exists_pow_le [CompactSpace X] {A B : X.IdealSheafData} (hB : B.ofFiniteType)
    (h : (A.support : Set X) ⊆ (B.support : Set X)) :
    ∃ n : ℕ, B ^ n ≤ A := by
  -- `V(A) ⊆ V(B)` says that `B` is contained in the radical of `A`
  have hrad : B ≤ A.radical := by
    rw [← vanishingIdeal_support]
    exact le_support_iff_le_vanishingIdeal.mp (SetLike.coe_subset_coe.mp h)
  -- on every affine open, a power of the ideal of `B` lies in the ideal of `A`
  have key : ∀ U : X.affineOpens, ∃ n : ℕ, B.ideal U ^ n ≤ A.ideal U := fun U ↦
    Ideal.exists_pow_le_of_le_radical_of_fg (by simpa using hrad U) (hB U le_top)
  choose n hn using key
  -- quasi-compactness bounds the exponents
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := by
    rw [← Opens.coe_iSup, iSup_affineOpens_eq_top]
    simp
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U.1 : Set X))
      (fun U ↦ U.1.2) hcov
  refine ⟨s.sup n, le_of_iSup_eq_top (fun U : {U : X.affineOpens // U ∈ s} ↦ U.1) ?_ ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  · rintro ⟨U, hU⟩
    refine le_trans ?_ (hn U)
    simpa using Ideal.pow_le_pow_right (I := B.ideal U) (Finset.le_sup hU)

end AlgebraicGeometry.Scheme.IdealSheafData
