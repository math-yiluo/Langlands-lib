/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Triangulated categories with a bounded t-structure are idempotent complete

Let `C` be a triangulated category with a bounded t-structure `t`. We show that every idempotent
of `C` splits, so that the canonical fully faithful functor `C ⥤ Karoubi C` is an equivalence.

The proof is by induction on the amplitude of an object `X` carrying an idempotent `p`. In
amplitude zero, `X` is a shift of an object of the heart, which is abelian and hence idempotent
complete (`CategoryTheory.Triangulated.TStructure.isIdempotentComplete_heart`). In general, let
`A ⟶ X ⟶ B ⟶ A⟦1⟧` be the truncation triangle cutting off the top cohomology of `X`. The
idempotent `p` induces idempotents `p_A` of `A` and `p_B` of `B`, which split by induction, say
through `A₁` and `B₁`. The connecting morphism restricts to `δ₁ : B₁ ⟶ A₁⟦1⟧`, and a cone `C₁`
of `δ₁` comes with morphisms of triangles `C₁ ⟶ X ⟶ C₁` composing to an automorphism. They
exhibit `C₁` as the image of an idempotent `q` of `X` inducing `p_A` and `p_B`, so that
`(p - q)² = 0`. Two idempotents whose difference has square zero are conjugate
(`CategoryTheory.Idempotents.exists_split_of_sub_comp_sub_eq_zero`), so `p` splits.

The blueprint deduces the theorem from the triangulated structure of the Karoubi envelope (the
theorem of Balmer and Schlichting) and the induced t-structure on it; the argument above runs
the same induction directly inside `C`.

## Main statements

- `CategoryTheory.Triangulated.TStructure.isIdempotentComplete_of_bounded`: a triangulated
  category with a bounded t-structure is idempotent complete.
- `CategoryTheory.Triangulated.TStructure.isEquivalence_toKaroubi_of_bounded`: the inclusion
  into the Karoubi envelope is an equivalence.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Triangulated.TStructure

open Category Limits Pretriangulated Idempotents Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (t : TStructure C)

/-- An idempotent of an object of the heart splits. -/
lemma isSplit_of_heart {X : C} (hX : t.heart X) {p : X ⟶ X} (hp : p ≫ p = p) : IsSplit p := by
  let := t.hasHeartFullSubcategory
  have h := (isIdempotentComplete_iff_isSplit.1
    (t.isIdempotentComplete_heart t.heart.FullSubcategory)) ⟨X, hX⟩
    (ObjectProperty.homMk p) (by ext; exact hp)
  exact h.map t.heart.ι

/-- An idempotent of an object concentrated in a single degree splits. -/
lemma isSplit_of_isLE_of_isGE {X : C} (a : ℤ) [t.IsLE X a] [t.IsGE X a] {p : X ⟶ X}
    (hp : p ≫ p = p) : IsSplit p := by
  have hX : t.heart (X⟦a⟧) :=
    (t.mem_heart_iff _).2 ⟨t.isLE_shift X a a 0 (by lia), t.isGE_shift X a a 0 (by lia)⟩
  have h := (t.isSplit_of_heart hX (p := p⟦a⟧') (by rw [← Functor.map_comp, hp])).map
    (shiftFunctor C (-a))
  exact h.of_iso ((shiftFunctorCompIsoId C a (-a) (by lia)).symm.app X)
    ((shiftFunctorCompIsoId C a (-a) (by lia)).inv.naturality p)

omit [IsTriangulated C] in
/-- The core of the inductive step: an idempotent `p` of the middle term of a distinguished
triangle `T`, compatible with idempotents `pA`, `pB` of the outer terms, splits if `pA` and `pB`
split through the outer terms of a distinguished triangle `T₁` whose connecting morphism is the
restriction of that of `T`:

```
  T₁.obj₁ ──T₁.mor₁──▶ T₁.obj₂ ──T₁.mor₂──▶ T₁.obj₃ ──T₁.mor₃──▶ T₁.obj₁⟦1⟧
   │  ▲                                       │  ▲
 iA│  │eA                                   iB│  │eB
   ▼  │                                       ▼  │
  T.obj₁ ──T.mor₁───▶ T.obj₂ ───T.mor₂───▶ T.obj₃ ───T.mor₃───▶ T.obj₁⟦1⟧
   ⟲ pA = eA ≫ iA        ⟲ p                 ⟲ pB = eB ≫ iB
```

with `iA ≫ eA = 𝟙` and `iB ≫ eB = 𝟙`, `p` compatible with `pA` and `pB`, and
`T₁.mor₃ = iB ≫ T.mor₃ ≫ eA⟦1⟧'`. -/
lemma isSplit_of_distTriang_aux (T T₁ : Triangle C) (hT : T ∈ distTriang C)
    (hT₁ : T₁ ∈ distTriang C) {p : T.obj₂ ⟶ T.obj₂} (hp : p ≫ p = p)
    {pA : T.obj₁ ⟶ T.obj₁} {pB : T.obj₃ ⟶ T.obj₃}
    (hA : T.mor₁ ≫ p = pA ≫ T.mor₁) (hB : p ≫ T.mor₂ = T.mor₂ ≫ pB)
    (hδ : pB ≫ T.mor₃ = T.mor₃ ≫ pA⟦(1 : ℤ)⟧')
    (iA : T₁.obj₁ ⟶ T.obj₁) (eA : T.obj₁ ⟶ T₁.obj₁) (hiA : iA ≫ eA = 𝟙 _) (heA : eA ≫ iA = pA)
    (iB : T₁.obj₃ ⟶ T.obj₃) (eB : T.obj₃ ⟶ T₁.obj₃) (hiB : iB ≫ eB = 𝟙 _) (heB : eB ≫ iB = pB)
    (hT₁δ : T₁.mor₃ = iB ≫ T.mor₃ ≫ eA⟦(1 : ℤ)⟧') :
    IsSplit p := by
  -- the morphism of triangles `T₁ ⟶ T`
  obtain ⟨φ, hφ₁, hφ₂⟩ := complete_distinguished_triangle_morphism₂ _ _ hT₁ hT iA iB (by
    rw [hT₁δ, assoc, assoc, ← Functor.map_comp, heA, ← hδ, ← heB, assoc, reassoc_of% hiB])
  -- the morphism of triangles `T ⟶ T₁`
  obtain ⟨ψ, hψ₁, hψ₂⟩ := complete_distinguished_triangle_morphism₂ _ _ hT hT₁ eA eB (by
    rw [hT₁δ, reassoc_of% heB, reassoc_of% hδ, ← Functor.map_comp, ← heA, assoc, hiA, comp_id])
  -- `φ ≫ ψ` is an automorphism of `T₁.obj₂`
  have hu : IsIso (φ ≫ ψ) := by
    let f : T₁ ⟶ T₁ := Triangle.homMk _ _ (𝟙 _) (φ ≫ ψ) (𝟙 _)
      (by rw [reassoc_of% hφ₁, hψ₁, reassoc_of% hiA, id_comp])
      (by rw [comp_id, assoc, ← hψ₂, ← reassoc_of% hφ₂, hiB, comp_id])
      (by simp)
    exact isIso₂_of_isIso₁₃ f hT₁ hT₁ (IsIso.id _)
      (IsIso.id _)
  have hu₁ : T₁.mor₁ ≫ inv (φ ≫ ψ) = T₁.mor₁ := by
    rw [IsIso.comp_inv_eq, reassoc_of% hφ₁, hψ₁, reassoc_of% hiA]
  have hu₂ : inv (φ ≫ ψ) ≫ T₁.mor₂ = T₁.mor₂ := by
    rw [IsIso.inv_comp_eq, assoc, ← hψ₂, ← reassoc_of% hφ₂, hiB, comp_id]
  -- the idempotent `q = ψ ≫ inv (φ ≫ ψ) ≫ φ` splits through `T₁.obj₂`
  let q := ψ ≫ inv (φ ≫ ψ) ≫ φ
  have hsq : IsSplit q := ⟨_, inv (φ ≫ ψ) ≫ φ, ψ, by simp, rfl⟩
  have hq : q ≫ q = q := by
    have := IsIso.hom_inv_id (φ ≫ ψ)
    simp only [assoc] at this
    simp only [q, assoc, reassoc_of% this]
  have hq₁ : T.mor₁ ≫ q = pA ≫ T.mor₁ := by
    simp only [q, reassoc_of% hψ₁, reassoc_of% hu₁, hφ₁, ← heA, assoc]
  have hq₂ : q ≫ T.mor₂ = T.mor₂ ≫ pB := by
    simp only [q, assoc, ← hφ₂, reassoc_of% hu₂, ← reassoc_of% hψ₂, ← heB]
  have h₁ : T.mor₁ ≫ (p - q) = 0 := by rw [comp_sub, hA, hq₁, sub_self]
  have h₂ : (p - q) ≫ T.mor₂ = 0 := by rw [sub_comp, hB, hq₂, sub_self]
  obtain ⟨d, hd⟩ := Triangle.yoneda_exact₂ T hT (p - q) h₁
  refine exists_split_of_sub_comp_sub_eq_zero hp hq ?_ hsq
  nth_rewrite 2 [hd]
  rw [← assoc, h₂, zero_comp]

omit [IsTriangulated C] in
/-- The inductive step: an idempotent `p` of the middle term of a distinguished triangle splits if
it is compatible with idempotents of the outer terms which split. -/
lemma isSplit_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C) {p : T.obj₂ ⟶ T.obj₂}
    (hp : p ≫ p = p) {pA : T.obj₁ ⟶ T.obj₁} {pB : T.obj₃ ⟶ T.obj₃}
    (hA : T.mor₁ ≫ p = pA ≫ T.mor₁) (hB : p ≫ T.mor₂ = T.mor₂ ≫ pB)
    (hδ : pB ≫ T.mor₃ = T.mor₃ ≫ pA⟦(1 : ℤ)⟧') (sA : IsSplit pA) (sB : IsSplit pB) :
    IsSplit p := by
  obtain ⟨A₁, iA, eA, hiA, heA⟩ := sA
  obtain ⟨B₁, iB, eB, hiB, heB⟩ := sB
  obtain ⟨C₁, u, v, hT₁⟩ := distinguished_cocone_triangle₂ (iB ≫ T.mor₃ ≫ eA⟦(1 : ℤ)⟧')
  exact isSplit_of_distTriang_aux T _ hT hT₁ hp hA hB hδ iA eA hiA heA iB eB hiB heB rfl

/-- An idempotent of an object of amplitude `[a, a + n]` splits. -/
lemma isSplit_of_isGE_of_isLE (n : ℕ) :
    ∀ (X : C) (a : ℤ) [t.IsGE X a] [t.IsLE X (a + n)] (p : X ⟶ X), p ≫ p = p → IsSplit p := by
  induction n with
  | zero =>
    intro X a _ h p hp
    have : t.IsLE X a := by simpa using h
    exact t.isSplit_of_isLE_of_isGE a hp
  | succ n ih =>
    intro X a _ h p hp
    have hT := t.triangleLEGE_distinguished (a + n) (a + n + 1) rfl X
    have : t.IsLE X (a + n + 1) := by simpa [add_assoc] using h
    refine isSplit_of_distTriang _ hT hp (pA := (t.truncLE (a + n)).map p)
      (pB := (t.truncGE (a + n + 1)).map p) ((t.truncLEι (a + n)).naturality p).symm
      ((t.truncGEπ (a + n + 1)).naturality p) ((t.truncGEδLE (a + n) (a + n + 1) rfl).naturality p)
      ?_ ?_
    · exact ih ((t.truncLE (a + n)).obj X) a _ (by rw [← Functor.map_comp, hp])
    · exact t.isSplit_of_isLE_of_isGE (X := (t.truncGE (a + n + 1)).obj X) (a + n + 1)
        (by rw [← Functor.map_comp, hp])

/-- A triangulated category with a bounded t-structure is idempotent complete, i.e. every idempotent
splits. -/
theorem isIdempotentComplete_of_bounded (ht : ∀ X : C, t.bounded X) : IsIdempotentComplete C := by
  rw [isIdempotentComplete_iff_isSplit]
  intro X p hp
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ht X
  have : t.IsLE X (a + ((b - a).toNat : ℕ)) := t.isLE_of_le X b _ (by lia)
  exact t.isSplit_of_isGE_of_isLE (b - a).toNat X a p hp

/-- For a triangulated category with a bounded t-structure, the canonical fully faithful functor
into the Karoubi envelope is an equivalence. -/
theorem isEquivalence_toKaroubi_of_bounded (ht : ∀ X : C, t.bounded X) :
    (toKaroubi C).IsEquivalence := by
  have := t.isIdempotentComplete_of_bounded ht
  infer_instance

end CategoryTheory.Triangulated.TStructure
