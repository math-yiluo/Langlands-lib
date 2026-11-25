/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The finite-sum reduction used in the repeated-tuple cancellation argument.
Proof: expand the alternating differential; every face outside the repeated positions
is zero by the repeated-tuple hypothesis, leaving exactly the displayed two-face sum.
(blueprint: lem-pc-cech-differential-repeated-decomposition) -/
theorem cechDifferential_repeated_decomposition (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (c : S.cochains F p) (t : Fin (p + 2) → I)
    (a b : Fin (p + 2)) (hab : a ≠ b) (htab : t a = t b)
    (hz : ∀ s : Fin (p + 1) → I, ¬ Function.Injective s → c s = 0) :
    S.differentialValue F p c t =
      ∑ j : ({a, b} : Finset (Fin (p + 2))),
        (-1 : ℤ) ^ (j : Fin (p + 2)).val •
          (F.map (S.indexMap t (j : Fin (p + 2)).succAbove).op)
            (c (t ∘ (j : Fin (p + 2)).succAbove)) := by
  classical
  let term (j : Fin (p + 2)) : F.obj (op (S.W (p + 1) t)) :=
    (-1 : ℤ) ^ j.val • (F.map (S.indexMap t j.succAbove).op) (c (t ∘ j.succAbove))
  change (∑ j, term j) = ∑ j : ({a, b} : Finset (Fin (p + 2))), term j
  rw [Finset.sum_coe_sort]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have hja : a ≠ j := by
    intro h
    subst j
    exact hj (by simp)
  have hjb : b ≠ j := by
    intro h
    subst j
    exact hj (by simp)
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hja
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hjb
  have hnon : ¬ Function.Injective (t ∘ j.succAbove) := by
    intro hinj
    have heq : a' = b' := hinj (by simpa [Function.comp_def, ha', hb'] using htab)
    apply hab
    rw [← ha', ← hb', heq]
  dsimp only [term]
  rw [hz _ hnon]
  simp

end AlgebraicGeometry.Scheme
