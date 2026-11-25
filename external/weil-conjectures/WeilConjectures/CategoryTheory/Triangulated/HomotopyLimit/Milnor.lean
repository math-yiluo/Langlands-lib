/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import WeilConjectures.Mathlib.CategoryTheory.CofilteredSystem

/-!
# The Milnor map of a homotopy limit of a tower

Let `c` be a homotopy limit cone over a tower `F : ℕᵒᵖ ⥤ C` in a pretriangulated category, so
that `c.pt = R lim F` sits in the Milnor triangle `R lim F → ∏ₙ Fₙ → ∏ₙ Fₙ → (R lim F)⟦1⟧`. For
an object `L`, the long exact sequence of `Hom(L, -)` gives the Milnor exact sequence

`0 → lim¹ₙ Hom(L⟦1⟧, Fₙ) → Hom(L, R lim F) → limₙ Hom(L, Fₙ) → 0`.

When the groups `Hom(L⟦1⟧, Fₙ)` are finite, their `lim¹` vanishes
(`AddCommGroup.exists_sub_map_succ_eq_of_finite`), so the *Milnor map*
`Hom(L, R lim F) → limₙ Hom(L, Fₙ)` is bijective. For `L` a shifted unit object these `Hom`
groups are the cohomology groups, which is the form used for `ℓ`-adic cohomology.

## Main results

- `CategoryTheory.Pretriangulated.IsHomotopyLimit.bijective_milnorMap`: the Milnor map is
  bijective when the groups `Hom(L⟦1⟧, Fₙ)` are finite.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The compatible families of maps `L ⟶ Fₙ` into a tower: the inverse limit
`limₙ Hom(L, Fₙ)`. -/
def towerHomLimit (F : ℕᵒᵖ ⥤ C) (L : C) : Type _ :=
  {x : ∀ n : ℕ, L ⟶ F.obj (op n) // ∀ n, x (n + 1) ≫ F.map (homOfLE n.le_succ).op = x n}

/-- The *Milnor map* `Hom(L, c.pt) → limₙ Hom(L, Fₙ)` of a cone over a tower. -/
def milnorMap {F : ℕᵒᵖ ⥤ C} (c : Cone F) (L : C) (f : L ⟶ c.pt) : towerHomLimit F L :=
  ⟨fun n ↦ f ≫ c.π.app (op n), fun n ↦ by rw [assoc, c.w]⟩

/-- *Mittag-Leffler vanishing* for homotopy limits: if `c` is a homotopy limit cone over a tower
`F` and the groups `Hom(L⟦1⟧, Fₙ)` are finite, then the Milnor map
`Hom(L, R lim F) → limₙ Hom(L, Fₙ)` is bijective. Its kernel is `lim¹ₙ Hom(L⟦1⟧, Fₙ)` by the
Milnor triangle, which vanishes for a tower of finite groups.
(blueprint: `lem-weil-pbc-mittag-leffler`) -/
theorem IsHomotopyLimit.bijective_milnorMap {F : ℕᵒᵖ ⥤ C} {c : Cone F}
    (hc : IsHomotopyLimit c) (L : C) [∀ n : ℕ, Finite (L⟦(1 : ℤ)⟧ ⟶ F.obj (op n))] :
    Function.Bijective (milnorMap c L) := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  refine ⟨fun f f' hff' ↦ ?_, fun x ↦ ?_⟩
  · -- a map `g : L ⟶ R lim F` with all `g ≫ c.π n = 0` vanishes
    rw [← sub_eq_zero]
    set g := f - f'
    have hg : g ≫ Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) = 0 :=
      Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
        have := congrArg (fun x : towerHomLimit F L ↦ x.1 n) hff'
        simp only [milnorMap] at this
        simp [g, Preadditive.sub_comp, this]
    obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₁ _ hT (g⟦(1 : ℤ)⟧') (by
      change g⟦(1 : ℤ)⟧' ≫ (Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)))⟦(1 : ℤ)⟧' = 0
      rw [← Functor.map_comp, hg, Functor.map_zero])
    -- `u : L⟦1⟧ ⟶ ∏ Fₙ` is in the image of `1 - t`, since `lim¹ Hom(L⟦1⟧, Fₙ) = 0`
    obtain ⟨v, hv⟩ := AddCommGroup.exists_sub_map_succ_eq_of_finite
      (G := fun n ↦ L⟦(1 : ℤ)⟧ ⟶ F.obj (op n))
      (fun n ↦ Preadditive.rightComp _ (F.map (homOfLE n.le_succ).op))
      (fun n ↦ u ≫ P.proj n)
    have hu' : u = Fan.IsLimit.lift hP v ≫ (𝟙 P.pt - towerShift hP) :=
      Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
        simp only [Preadditive.comp_sub, comp_id, Preadditive.sub_comp, assoc,
          towerShift_proj, Fan.IsLimit.fac_assoc, Fan.IsLimit.fac]
        exact (hv n).symm
    have h0 : g⟦(1 : ℤ)⟧' = 0 := by
      rw [hu, hu', assoc]
      have : (𝟙 P.pt - towerShift hP) ≫ δ = 0 := comp_distTriang_mor_zero₂₃ _ hT
      erw [this, comp_zero]
    exact (shiftFunctor C (1 : ℤ)).map_eq_zero_iff.mp h0
  · -- a compatible family lifts along `R lim F → ∏ Fₙ`
    obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂ _ hT (Fan.IsLimit.lift hP x.1) (by
      refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
      simp only [Triangle.mk_mor₂, Preadditive.comp_sub, Preadditive.sub_comp, assoc,
        towerShift_proj, Fan.IsLimit.fac_assoc, zero_comp]
      erw [Category.id_comp, Fan.IsLimit.fac, x.2 n, sub_self])
    refine ⟨u, Subtype.ext (funext fun n ↦ ?_)⟩
    have := congrArg (· ≫ P.proj n) hu
    simp only [Triangle.mk_mor₁, Fan.IsLimit.fac, assoc] at this
    exact this.symm

end CategoryTheory.Pretriangulated
