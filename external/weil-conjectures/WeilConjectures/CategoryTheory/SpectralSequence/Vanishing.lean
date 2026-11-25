/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck

/-!
# Vanishing of the abutment of a first quadrant spectral sequence

If all the `E₂`-terms `E₂^{p, q}` of total degree `p + q = n` of a first quadrant cohomological
spectral sequence vanish, so do all the later pages in these spots, hence the `E∞`-terms, and
the abutment in degree `n` vanishes (`CategoryTheory.SpectralSequence.AbutsTo.isZero`).

Applied to the Grothendieck spectral sequence `RᵖG RᵠF X ⟹ Rᵖ⁺ᵠ(F ⋙ G) X`, this gives
`Rⁿ(F ⋙ G) X = 0` as soon as `RᵖG RᵠF X = 0` whenever `p + q = n`
(`CategoryTheory.Functor.isZero_rightDerived_comp_of_isZero`), and in particular
`Rⁿ(F ⋙ G) X = 0` for `n > c + e` if `RᵠF X = 0` for `q > e` and `RᵖG` kills the `RᵠF X` for
`p > c` (`CategoryTheory.Functor.isZero_rightDerived_comp_of_lt_add`).
-/

@[expose] public section

universe v u v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace SpectralSequence

variable {E : E₂CohomologicalSpectralSequenceNat C}

/-- A spot of a first quadrant spectral sequence which vanishes on the `E₂`-page vanishes on all
later pages: each page is the homology of the previous one. -/
lemma isZero_page_of_isZero_page_two {pq : ℕ × ℕ} (h : IsZero ((E.page 2).X pq)) (r : ℤ)
    (hr : 2 ≤ r) : IsZero ((E.page r).X pq) := by
  induction r, hr using Int.leInduction with
  | base => exact h
  | succ r hr ih =>
    exact ((E.page r).sc pq).isZero_homology_of_isZero_X₂ ih |>.of_iso (E.iso r (r + 1) pq).symm

/-- A spot of a first quadrant spectral sequence which vanishes on the `E₂`-page has vanishing
`E∞`-term. -/
lemma isZero_pageInfinity_of_isZero_page_two {pq : ℕ × ℕ} (h : IsZero ((E.page 2).X pq)) :
    IsZero (E.pageInfinity pq) :=
  isZero_page_of_isZero_page_two h _ (by lia)

/-- **Vanishing of the abutment.** If `E` abuts to `H` and all the `E₂`-terms of total degree `n`
vanish, then `H n` vanishes. -/
theorem AbutsTo.isZero {H : ℕ → C} (hE : E.AbutsTo H) (n : ℕ)
    (h : ∀ p q : ℕ, p + q = n → IsZero ((E.page 2).X (p, q))) : IsZero (H n) := by
  obtain ⟨A⟩ := hE
  -- each step of the filtration of `H n` is an equality
  have step (p : ℕ) (hp : p ≤ n) : A.filtration n (p + 1) = A.filtration n p := by
    obtain ⟨e⟩ := A.nonempty_gradedIso n p (n - p) (by lia)
    have hz : IsZero (cokernel (Subobject.ofLE _ _ (A.filtration_succ_le n p))) :=
      (isZero_pageInfinity_of_isZero_page_two (h p (n - p) (by lia))).of_iso e
    have : Epi (Subobject.ofLE _ _ (A.filtration_succ_le n p)) :=
      Preadditive.epi_of_isZero_cokernel _ hz
    have := isIso_of_mono_of_epi (Subobject.ofLE _ _ (A.filtration_succ_le n p))
    refine le_antisymm (A.filtration_succ_le n p) (Subobject.le_of_comm
      (inv (Subobject.ofLE _ _ (A.filtration_succ_le n p))) ?_)
    rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow]
  have htop (p : ℕ) (hp : p ≤ n + 1) : A.filtration n p = ⊤ := by
    induction p with
    | zero => exact A.filtration_zero n
    | succ p ih => rw [step p (by lia), ih (by lia)]
  have hbot : (⊤ : Subobject (H n)) = ⊥ := (htop (n + 1) le_rfl).symm.trans
    (A.filtration_succ_self n)
  by_contra hH
  have := Subobject.nontrivial_of_not_isZero hH
  exact top_ne_bot hbot

end SpectralSequence

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]

/-- **Vanishing from the Grothendieck spectral sequence.** For a composable pair with acyclicity
`(F, G)`, if `RᵖG (RᵠF X) = 0` whenever `p + q = n`, then `Rⁿ(F ⋙ G) X = 0`. -/
theorem Functor.isZero_rightDerived_comp_of_isZero (F : A ⥤ B) (G : B ⥤ C) [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) (n : ℕ)
    (h : ∀ p q : ℕ, p + q = n → IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj X))) :
    IsZero (((F ⋙ G).rightDerived n).obj X) := by
  obtain ⟨E, hE, habut⟩ := F.exists_grothendieckSpectralSequence G hFG X
  exact habut.isZero n fun p q hpq ↦ (h p q hpq).of_iso (hE p q).some

/-- **Amplitude from the Grothendieck spectral sequence.** For a composable pair with acyclicity
`(F, G)`, if `RᵠF X = 0` for `q > e` and `RᵖG (RᵠF X) = 0` for `p > c` and every `q`, then
`Rⁿ(F ⋙ G) X = 0` for `n > c + e`. -/
theorem Functor.isZero_rightDerived_comp_of_lt_add (F : A ⥤ B) (G : B ⥤ C) [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) {c e : ℕ}
    (hF : ∀ q : ℕ, e < q → IsZero ((F.rightDerived q).obj X))
    (hG : ∀ p q : ℕ, c < p → IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj X)))
    (n : ℕ) (hn : c + e < n) : IsZero (((F ⋙ G).rightDerived n).obj X) := by
  refine F.isZero_rightDerived_comp_of_isZero G hFG X n fun p q hpq ↦ ?_
  by_cases hq : e < q
  · exact Functor.map_isZero _ (hF q hq)
  · exact hG p q (by lia)

end CategoryTheory
