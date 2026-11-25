/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterTower
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterComplete

/-!
# Lifting compatible retractions to a complete object

Let `C` be a pretriangulated category, `z` an element of the center of `C` commuting with the
shifts (for instance the multiplication by an integer `m`) and `A` a `z`-complete object
(`CategoryTheory.Pretriangulated.IsCenterComplete`). Think of `A` as a complex of
`ℤ_ℓ`-modules, `z = ℓ`, and of objects `Qₙ` as its reductions `A ⊗ᴸ ℤ/ℓⁿ⁺¹`, with the reduction
maps `η₀ : A ⟶ Q₀`, the transitions `tₙ : Qₙ₊₁ ⟶ Qₙ` and the Bockstein maps `δₙ : Qₙ ⟶ A⟦1⟧`,
which satisfy `tₙ ≫ δₙ = δₙ₊₁ ≫ z` and such that `A --z--> A --η₀--> Q₀ --δ₀--> A⟦1⟧` is
distinguished.

* `CategoryTheory.Pretriangulated.IsCenterComplete.eq_zero_of_comp_app_eq`: a family of maps
  `oₙ : B ⟶ K` into a complete object with `oₙ₊₁ ≫ z = oₙ` vanishes. It is a cone over the tower
  `⋯ --z--> K --z--> K`, whose homotopy limit vanishes.
* `CategoryTheory.Pretriangulated.exists_comp_eq_of_tower`: a compatible family of maps
  `ρₙ : B ⟶ Qₙ` lifts at level `0` to a map `r : B ⟶ A` with `r ≫ η₀ = ρ₀`. The obstruction
  `ρ₀ ≫ δ₀` is the first term of the family `ρₙ ≫ δₙ`, which vanishes by the previous point.
  This is the surjectivity half of the Milnor sequence for `A = R lim Qₙ`; no `lim¹` term has
  to vanish.
* `CategoryTheory.Pretriangulated.isSplitMono_of_tower`: **lifting split monomorphisms**. Let
  `i : A ⟶ B` and let `ρₙ : B ⟶ Qₙ` be compatible with `i ≫ ρ₀ = η₀`, for instance
  `ρₙ = ηₙ(B) ≫ rₙ` for compatible retractions `rₙ` of the reductions of `i`. If every
  endomorphism `e` of `A` with `e ≫ η₀ = η₀` is invertible (derived Nakayama), then `i` is a
  split monomorphism: for the lift `r` of `ρ₀`, `i ≫ r` is such an endomorphism, and
  `r ≫ (i ≫ r)⁻¹` is a retraction of `i`.

That complete objects are stable under shifts and extensions
(`CategoryTheory.Pretriangulated.IsCenterComplete.shift`,
`CategoryTheory.Pretriangulated.IsCenterComplete.ext₂`) is in
`WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterComplete`.
-/

@[expose] public section

namespace CategoryTheory.CatCenter

variable {D : Type*} [Category* D] [Preadditive D]

/-- The multiple `m • 1` of the unit of the center acts by `m • 𝟙`. -/
@[simp]
lemma zsmul_one_app (m : ℤ) (X : D) : (m • (1 : CatCenter D)).app X = m • 𝟙 X :=
  NatTrans.app_zsmul X _ m

/-- The multiple `m • 1` of the unit of the center commutes with the shifts. -/
lemma zsmul_one_app_shift [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] (m : ℤ) (X : D)
    (n : ℤ) : (m • (1 : CatCenter D)).app (X⟦n⟧) = ((m • (1 : CatCenter D)).app X)⟦n⟧' := by
  rw [zsmul_one_app, zsmul_one_app, Functor.map_zsmul, CategoryTheory.Functor.map_id]

end CategoryTheory.CatCenter

namespace CategoryTheory.Pretriangulated

open Category Limits _root_.Opposite

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A family of maps `oₙ : B ⟶ K` into a complete object `K` such that `oₙ₊₁ ≫ z_K = oₙ`
vanishes: it is a cone over the tower `⋯ --z--> K --z--> K`, whose homotopy limit vanishes. -/
lemma IsCenterComplete.eq_zero_of_comp_app_eq {z : CatCenter C}
    (hz : ∀ X : C, z.app (X⟦(1 : ℤ)⟧) = (z.app X)⟦(1 : ℤ)⟧') {K : C}
    (hK : IsCenterComplete z K) [HasProduct fun _ : ℕ ↦ K] {B : C} (o : ℕ → (B ⟶ K))
    (ho : ∀ n, o (n + 1) ≫ z.app K = o n) (n : ℕ) : o n = 0 := by
  have : HasProduct fun n : ℕ ↦ (centerTower z K).obj (op n) := by
    dsimp
    infer_instance
  obtain ⟨c, hc⟩ := exists_isHomotopyLimit (centerTower z K)
  let s : Cone (centerTower z K) :=
    { pt := B
      π := NatTrans.ofOpSequence (fun n ↦ o n) fun n ↦ by
        rw [centerTower_map_succ]
        exact (id_comp _).trans (ho n).symm }
  obtain ⟨l, hl⟩ := hc.exists_lift s
  have h := hl n
  rw [(hK.isZero_of_isHomotopyLimit hz hc).eq_of_tgt l 0, zero_comp] at h
  exact h.symm

variable {z : CatCenter C} (hz : ∀ (X : C) (n : ℤ), z.app (X⟦n⟧) = (z.app X)⟦n⟧') {A : C}
  (hA : IsCenterComplete z A) [HasProduct fun _ : ℕ ↦ A⟦(1 : ℤ)⟧] {Q : ℕ → C} (η₀ : A ⟶ Q 0)
  (t : ∀ n, Q (n + 1) ⟶ Q n) (δ : ∀ n, Q n ⟶ A⟦(1 : ℤ)⟧)
  (hδ : ∀ n, t n ≫ δ n = δ (n + 1) ≫ z.app (A⟦(1 : ℤ)⟧)) (a : A ⟶ A)
  (hT : Triangle.mk a η₀ (δ 0) ∈ distTriang C)
include hz hA hδ hT

/-- **Lifting a compatible family to a complete object.** If `A` is complete, the maps
`δₙ : Qₙ ⟶ A⟦1⟧` satisfy `tₙ ≫ δₙ = δₙ₊₁ ≫ z` and `A ⟶ A --η₀--> Q₀ --δ₀--> A⟦1⟧` is
distinguished, then for every family `ρₙ : B ⟶ Qₙ` with `ρₙ₊₁ ≫ tₙ = ρₙ`, the map `ρ₀` lifts
along `η₀`: the obstructions `ρₙ ≫ δₙ` form a family as in
`CategoryTheory.Pretriangulated.IsCenterComplete.eq_zero_of_comp_app_eq`, hence vanish. -/
lemma exists_comp_eq_of_tower {B : C} (ρ : ∀ n, B ⟶ Q n) (hρ : ∀ n, ρ (n + 1) ≫ t n = ρ n) :
    ∃ r : B ⟶ A, r ≫ η₀ = ρ 0 := by
  have h₀ : ρ 0 ≫ δ 0 = 0 :=
    (hA.shift hz 1).eq_zero_of_comp_app_eq (fun X ↦ hz X 1) (fun n ↦ ρ n ≫ δ n)
      (fun n ↦ by rw [assoc, ← hδ, ← assoc, hρ]) 0
  obtain ⟨r, hr⟩ := Triangle.coyoneda_exact₃ _ hT (ρ 0) h₀
  exact ⟨r, hr.symm⟩

/-- **Lifting split monomorphisms to a complete object.** Let `i : A ⟶ B` be a morphism from a
complete object and `ρₙ : B ⟶ Qₙ` a compatible family with `i ≫ ρ₀ = η₀` (for instance
`ρₙ = ηₙ(B) ≫ rₙ` for compatible retractions `rₙ` of the reductions of `i`). If every
endomorphism `e` of `A` with `e ≫ η₀ = η₀` is an isomorphism (derived Nakayama), then `i` is a
split monomorphism. -/
theorem isSplitMono_of_tower {B : C} (i : A ⟶ B) (ρ : ∀ n, B ⟶ Q n)
    (hρ : ∀ n, ρ (n + 1) ≫ t n = ρ n) (hi : i ≫ ρ 0 = η₀)
    (hN : ∀ e : A ⟶ A, e ≫ η₀ = η₀ → IsIso e) : IsSplitMono i := by
  obtain ⟨r, hr⟩ := exists_comp_eq_of_tower hz hA η₀ t δ hδ a hT ρ hρ
  have := hN (i ≫ r) (by rw [assoc, hr, hi])
  exact IsSplitMono.mk' ⟨r ≫ inv (i ≫ r), by rw [← assoc, IsIso.hom_inv_id]⟩

end CategoryTheory.Pretriangulated
