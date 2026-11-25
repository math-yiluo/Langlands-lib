/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!

# Additivity of a pairing along three distinguished rows

Let `C` be a pretriangulated category and consider three distinguished triangles (the *rows*)
```
P₀ ⟶ Q₀ ⟶ R₀ ⟶ P₀⟦1⟧,    P₁ ⟶ Q₁ ⟶ R₁ ⟶ P₁⟦1⟧,    P₂ ⟶ Q₂ ⟶ R₂ ⟶ P₂⟦1⟧,
```
with morphisms of the first two terms `f : row₀ ⟶ row₁` and `g : row₂ ⟶ row₀` such that
`g ≫ f = 0` on the middle and last terms. Think of the rows as `K' ⊠ N ⟶ K ⊠ N ⟶ K'' ⊠ N` for a
distinguished triangle `K' ⟶ K ⟶ K''` and `N = D K, D K', D K''`, and of `f`, `g` as induced by
`D K ⟶ D K'` and `D K'' ⟶ D K`. Given `e : Q₀ ⟶ W`, `e₁ : P₁ ⟶ W`, `e₂ : R₂ ⟶ W` which are
dinatural (`ε₀ ≫ e = f ≫ e₁` on `P₀`, `g ≫ e = η₂ ≫ e₂` on `Q₂`) and sections `σ : T ⟶ Q₀`,
`σ₁ : T ⟶ P₁`, `σ₂ : T ⟶ R₂` which are compatible (`σ ≫ f = σ₁ ≫ ε₁`, `σ ≫ η₀ = σ₂ ≫ g`), the
pairing is additive,
```
σ ≫ e = σ₁ ≫ e₁ + σ₂ ≫ e₂,
```
as soon as a few morphism groups vanish: `T ⟶ R₁⟦-1⟧`, `P₀ ⟶ R₁⟦-1⟧`, `Q₂ ⟶ R₁⟦-1⟧` and
`P₂⟦1⟧ ⟶ W` (`CategoryTheory.Pretriangulated.comp_eq_add_of_distTriang`).

This is the triangulated core of the additivity of trace classes along an invariant open–closed
decomposition (blueprint `proposition-additivity-trace-classes--2`,
`proposition-additivity-trace-classes`): there `T` is the class of the support of a correspondence,
`W` the pushforward of the dualizing complex along the diagonal, `e` the evaluation kernels and `σ`
the supported classes. The filtered argument of Varshavsky, Prop. 1.5.10 (after SGA 5, III 4.13) is
replaced by the pullback `G` of the row `0` along `g : R₂ ⟶ R₀` (the cocone of `R₂ ⟶ R₀ ⟶ P₀⟦1⟧`):
the section lifts to `G`, and the defect of additivity on `G` vanishes on `P₀` and on `Q₂`, hence
factors through `P₂⟦1⟧`, where it is zero because the corner `P₂ = K' ⊠ D K''` does not meet the
diagonal.

-/

@[expose] public section

open CategoryTheory Limits Category Preadditive

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]


section Mk

variable {X Y Z A : C} {f : X ⟶ Y} {g : Y ⟶ Z} {δ : Z ⟶ X⟦(1 : ℤ)⟧}
  (h : Triangle.mk f g δ ∈ distTriang C)
include h

/-- `Triangle.coyoneda_exact₂` for a triangle given by `Triangle.mk`. -/
lemma exists_eq_comp_mor₁_of_comp_eq_zero (x : A ⟶ Y) (hx : x ≫ g = 0) :
    ∃ y : A ⟶ X, x = y ≫ f :=
  Triangle.coyoneda_exact₂ _ h x hx

/-- `Triangle.coyoneda_exact₃` for a triangle given by `Triangle.mk`. -/
lemma exists_eq_comp_mor₂_of_comp_eq_zero (x : A ⟶ Z) (hx : x ≫ δ = 0) :
    ∃ y : A ⟶ Y, x = y ≫ g :=
  Triangle.coyoneda_exact₃ _ h x hx

/-- `Triangle.yoneda_exact₂` for a triangle given by `Triangle.mk`. -/
lemma exists_eq_mor₂_comp_of_comp_eq_zero (x : Y ⟶ A) (hx : f ≫ x = 0) :
    ∃ y : Z ⟶ A, x = g ≫ y :=
  Triangle.yoneda_exact₂ _ h x hx

/-- `Triangle.yoneda_exact₃` for a triangle given by `Triangle.mk`. -/
lemma exists_eq_mor₃_comp_of_comp_eq_zero (x : Z ⟶ A) (hx : g ≫ x = 0) :
    ∃ y : X⟦(1 : ℤ)⟧ ⟶ A, x = δ ≫ y :=
  Triangle.yoneda_exact₃ _ h x hx

/-- A morphism to the first object of a distinguished triangle which vanishes after the first
morphism vanishes, if every morphism to the shifted third object `Z⟦-1⟧` does. -/
lemma eq_zero_of_comp_mor₁_eq_zero (hA : ∀ φ : A ⟶ Z⟦(-1 : ℤ)⟧, φ = 0) {x : A ⟶ X}
    (hx : x ≫ f = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ h) x hx
  rw [hA y, zero_comp]

/-- Two morphisms to the first object of a distinguished triangle which agree after the first
morphism are equal, if every morphism to the shifted third object `Z⟦-1⟧` vanishes. -/
lemma eq_of_comp_mor₁_eq (hA : ∀ φ : A ⟶ Z⟦(-1 : ℤ)⟧, φ = 0) {x x' : A ⟶ X}
    (hx : x ≫ f = x' ≫ f) : x = x' :=
  sub_eq_zero.1 (eq_zero_of_comp_mor₁_eq_zero h hA (by rw [sub_comp, hx, sub_self]))

omit h in
/-- A morphism of distinguished triangles `(𝟙, ?, c)` from the cocone of `c ≫ δ` to the triangle
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧`. -/
lemma exists_comp_eq_of_distTriang_comp (h : Triangle.mk f g δ ∈ distTriang C) {Y' Z' : C}
    {a : X ⟶ Y'} {π : Y' ⟶ Z'} (c : Z' ⟶ Z) (h' : Triangle.mk a π (c ≫ δ) ∈ distTriang C) :
    ∃ b : Y' ⟶ Y, a ≫ b = f ∧ π ≫ c = b ≫ g := by
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ _ _ h' h (𝟙 X) c (by
    change (c ≫ δ) ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 X) = c ≫ δ
    rw [CategoryTheory.Functor.map_id, comp_id])
  exact ⟨b, hb₁.trans (id_comp _), hb₂⟩

end Mk

variable {P₀ Q₀ R₀ P₁ Q₁ R₁ P₂ Q₂ R₂ T W : C}
  {ε₀ : P₀ ⟶ Q₀} {η₀ : Q₀ ⟶ R₀} {δ₀ : R₀ ⟶ P₀⟦(1 : ℤ)⟧}
  {ε₁ : P₁ ⟶ Q₁} {η₁ : Q₁ ⟶ R₁} {δ₁ : R₁ ⟶ P₁⟦(1 : ℤ)⟧}
  {ε₂ : P₂ ⟶ Q₂} {η₂ : Q₂ ⟶ R₂} {δ₂ : R₂ ⟶ P₂⟦(1 : ℤ)⟧}

/-- **Additivity of a dinatural pairing along three distinguished rows.** See the module
docstring for the notation. -/
theorem comp_eq_add_of_distTriang
    (h₀ : Triangle.mk ε₀ η₀ δ₀ ∈ distTriang C) (h₁ : Triangle.mk ε₁ η₁ δ₁ ∈ distTriang C)
    (h₂ : Triangle.mk ε₂ η₂ δ₂ ∈ distTriang C)
    (fP : P₀ ⟶ P₁) (fQ : Q₀ ⟶ Q₁) (fR : R₀ ⟶ R₁) (gQ : Q₂ ⟶ Q₀) (gR : R₂ ⟶ R₀)
    (hfP : ε₀ ≫ fQ = fP ≫ ε₁) (hfR : η₀ ≫ fR = fQ ≫ η₁) (hgR : η₂ ≫ gR = gQ ≫ η₀)
    (hgfQ : gQ ≫ fQ = 0) (hgfR : gR ≫ fR = 0)
    (e : Q₀ ⟶ W) (e₁ : P₁ ⟶ W) (e₂ : R₂ ⟶ W)
    (he₁ : ε₀ ≫ e = fP ≫ e₁) (he₂ : gQ ≫ e = η₂ ≫ e₂)
    (σ : T ⟶ Q₀) (σ₁ : T ⟶ P₁) (σ₂ : T ⟶ R₂)
    (hσ₁ : σ ≫ fQ = σ₁ ≫ ε₁) (hσ₂ : σ ≫ η₀ = σ₂ ≫ gR)
    (hT : ∀ φ : T ⟶ R₁⟦(-1 : ℤ)⟧, φ = 0) (hP : ∀ φ : P₀ ⟶ R₁⟦(-1 : ℤ)⟧, φ = 0)
    (hQ : ∀ φ : Q₂ ⟶ R₁⟦(-1 : ℤ)⟧, φ = 0) (hW : ∀ φ : P₂⟦(1 : ℤ)⟧ ⟶ W, φ = 0) :
    σ ≫ e = σ₁ ≫ e₁ + σ₂ ≫ e₂ := by
  -- the pullback `G` of the row `0` along `gR`
  obtain ⟨G, a, π, hG⟩ := distinguished_cocone_triangle₂ (gR ≫ δ₀)
  obtain ⟨πQ, hπQ₁, hπQ₂⟩ := exists_comp_eq_of_distTriang_comp h₀ gR hG
  have hηδ₀ : η₀ ≫ δ₀ = 0 := comp_distTriang_mor_zero₂₃ _ h₀
  have ha : a ≫ π = 0 := comp_distTriang_mor_zero₁₂ _ hG
  -- a lift of `πQ ≫ fQ` through `ε₁`
  obtain ⟨q, hq⟩ := exists_eq_comp_mor₁_of_comp_eq_zero h₁ (πQ ≫ fQ) (by
    rw [assoc, ← hfR, ← assoc, ← hπQ₂, assoc, hgfR, comp_zero])
  -- the lift of the section to `G`
  obtain ⟨s₁, hs₁⟩ := exists_eq_comp_mor₂_of_comp_eq_zero hG σ₂ (by
    rw [← assoc, ← hσ₂, assoc, hηδ₀, comp_zero])
  obtain ⟨z, hz⟩ := exists_eq_comp_mor₁_of_comp_eq_zero h₀ (s₁ ≫ πQ - σ) (by
    rw [sub_comp, assoc, ← hπQ₂, ← assoc, ← hs₁, hσ₂, sub_self])
  let s := s₁ - z ≫ a
  have hsQ : s ≫ πQ = σ := by
    rw [← sub_sub_cancel (s₁ ≫ πQ) σ, hz]
    simp only [s, sub_comp, assoc, hπQ₁]
  have hsR : s ≫ π = σ₂ := by
    simp only [s, sub_comp, assoc, ha, comp_zero, sub_zero, ← hs₁]
  have hsq : s ≫ q = σ₁ := eq_of_comp_mor₁_eq h₁ hT (by
    rw [assoc, ← hq, ← assoc, hsQ, hσ₁])
  -- the lift of `η₂` to `G`
  obtain ⟨b₁, hb₁⟩ := exists_eq_comp_mor₂_of_comp_eq_zero hG η₂ (by
    rw [← assoc, hgR, assoc, hηδ₀, comp_zero])
  obtain ⟨z', hz'⟩ := exists_eq_comp_mor₁_of_comp_eq_zero h₀ (b₁ ≫ πQ - gQ) (by
    rw [sub_comp, assoc, ← hπQ₂, ← assoc, ← hb₁, hgR, sub_self])
  let b := b₁ - z' ≫ a
  have hbQ : b ≫ πQ = gQ := by
    rw [← sub_sub_cancel (b₁ ≫ πQ) gQ, hz']
    simp only [b, sub_comp, assoc, hπQ₁]
  have hbR : b ≫ π = η₂ := by
    simp only [b, sub_comp, assoc, ha, comp_zero, sub_zero, ← hb₁]
  have hbq : b ≫ q = 0 := eq_zero_of_comp_mor₁_eq_zero h₁ hQ (by
    rw [assoc, ← hq, ← assoc, hbQ, hgfQ])
  have haq : a ≫ q = fP := eq_of_comp_mor₁_eq h₁ hP (by
    rw [assoc, ← hq, ← assoc, hπQ₁, hfP])
  -- the defect of additivity on `G` vanishes
  let D := πQ ≫ e - q ≫ e₁ - π ≫ e₂
  have hD : D = 0 := by
    obtain ⟨D'', hD''⟩ := exists_eq_mor₂_comp_of_comp_eq_zero hG D (by
      simp only [D, comp_sub, ← assoc, hπQ₁, haq, ha, zero_comp, he₁, sub_self])
    obtain ⟨Z, hZ⟩ := exists_eq_mor₃_comp_of_comp_eq_zero h₂ D'' (by
      rw [← hbR, assoc, ← hD'']
      simp only [D, comp_sub, ← assoc, hbQ, hbq, hbR, zero_comp, sub_zero, he₂, sub_self])
    rw [hD'', hZ, hW Z, comp_zero, comp_zero]
  have key : s ≫ D = 0 := by rw [hD, comp_zero]
  simp only [D, comp_sub, ← assoc, hsQ, hsq, hsR] at key
  rw [← sub_eq_zero, ← key, sub_sub]

end CategoryTheory.Pretriangulated
