/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Removing trivial summands from an octahedron

In a pretriangulated category `D`, consider composable morphisms `u₁₂ : X₁ ⟶ X₂` and
`u₂₃ : X₂ ⟶ X₃` with distinguished triangles on `u₁₂`, `u₂₃` and `u₁₂ ≫ u₂₃`. Padding one of the
objects `Xᵢ` by a direct summand on which the morphisms vanish, and the triangles by trivial
triangles, an octahedron for the padded data gives one for the original data, provided the
distinguished triangles of `D` are stable under retracts. This is the key step of the proof by
Balmer and Schlichting that the Karoubi envelope of a triangulated category satisfies the
octahedral axiom: the padded octahedron, once made block diagonal by an automorphism of its middle
object, has the original octahedron as a retract.

## Main statements

- `CategoryTheory.Pretriangulated.mk_comp_inl_distinguished`,
  `CategoryTheory.Pretriangulated.mk_fst_comp_distinguished`: the sum of a distinguished
  triangle with a trivial triangle is distinguished.
- `CategoryTheory.Triangulated.nonempty_octahedron_of_pad₁`,
  `CategoryTheory.Triangulated.nonempty_octahedron_of_pad₂`,
  `CategoryTheory.Triangulated.nonempty_octahedron_of_pad₃`: removing a trivial summand of `X₁`,
  `X₂` or `X₃` from an octahedron.

## References

* Paul Balmer and Marco Schlichting, *Idempotent completion of triangulated categories*,
  J. Algebra 236 (2001), proof of Theorem 1.12
-/
@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Pretriangulated

/-- The sum of a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` with the trivial triangle
`0 ⟶ C ⟶ C ⟶ 0` is distinguished. -/
lemma mk_comp_inl_distinguished {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang D) (C : D) :
    Triangle.mk (f ≫ biprod.inl : X ⟶ Y ⊞ C) (biprod.map g (𝟙 C)) (biprod.fst ≫ h) ∈
      distTriang D := by
  obtain ⟨Q, g', h', hT'⟩ := distinguished_cocone_triangle (f ≫ (biprod.inl : Y ⟶ Y ⊞ C))
  obtain ⟨a, ha₂, ha₃⟩ : ∃ a : Z ⟶ Q, g ≫ a = biprod.inl ≫ g' ∧ h ≫ (𝟙 X)⟦(1 : ℤ)⟧' = a ≫ h' :=
    complete_distinguished_triangle_morphism _ _ hT hT' (𝟙 X) biprod.inl (id_comp _).symm
  obtain ⟨b, hb₂, hb₃⟩ : ∃ b : Q ⟶ Z, g' ≫ b = biprod.fst ≫ g ∧ h' ≫ (𝟙 X)⟦(1 : ℤ)⟧' = b ≫ h :=
    complete_distinguished_triangle_morphism _ _ hT' hT (𝟙 X) biprod.fst
      (by change (f ≫ biprod.inl) ≫ biprod.fst = 𝟙 X ≫ f; simp)
  obtain ⟨d, hd⟩ : ∃ d : Q ⟶ C, biprod.snd = g' ≫ d :=
    Triangle.yoneda_exact₂ _ hT' (biprod.snd : Y ⊞ C ⟶ C)
      (by change (f ≫ biprod.inl) ≫ biprod.snd = 0; simp)
  rw [Functor.map_id, comp_id] at ha₃ hb₃
  have hg : g ≫ a ≫ b = g := by rw [reassoc_of% ha₂, hb₂, biprod.inl_fst_assoc]
  have hh : (a ≫ b) ≫ h = h := by rw [assoc, ← hb₃, ha₃]
  have : IsIso (a ≫ b) := by
    let φ : Triangle.mk f g h ⟶ Triangle.mk f g h :=
      Triangle.homMk _ _ (𝟙 _) (𝟙 _) (a ≫ b) (by simp) (by simpa using hg) (by simpa using hh.symm)
    exact isIso₃_of_isIso₁₂ φ hT hT (inferInstanceAs (IsIso (𝟙 _))) (inferInstanceAs (IsIso (𝟙 _)))
  have hg' : g ≫ inv (a ≫ b) = g := by rw [IsIso.comp_inv_eq, hg]
  have hh' : inv (a ≫ b) ≫ h = h := by rw [IsIso.inv_comp_eq, hh]
  let a' := inv (a ≫ b) ≫ a
  have ha'b : a' ≫ b = 𝟙 _ := by simp [a']
  have ha'₂ : g ≫ a' = biprod.inl ≫ g' := by rw [reassoc_of% hg', ha₂]
  have ha'₃ : a' ≫ h' = h := by rw [assoc, ← ha₃, hh']
  let d' := d - b ≫ a' ≫ d
  have hd' : g' ≫ d' = biprod.snd := by
    simp only [d', comp_sub, reassoc_of% hb₂, reassoc_of% ha'₂, ← hd, biprod.inl_snd,
      comp_zero, sub_zero]
  let Φ : Z ⊞ C ⟶ Q := biprod.desc a' (biprod.inr ≫ g')
  let Ψ : Q ⟶ Z ⊞ C := biprod.lift b d'
  have hΦΨ : Φ ≫ Ψ = 𝟙 _ := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    · simp [Φ, Ψ, ha'b]
    · simp [Φ, Ψ, d', reassoc_of% ha'b]
    · simp [Φ, Ψ, hb₂]
    · simp [Φ, Ψ, d', reassoc_of% hb₂, ← hd]
  have hΨ₂ : g' ≫ Ψ = biprod.map g (𝟙 C) := by
    apply biprod.hom_ext
    · simp [Ψ, hb₂]
    · simp [Ψ, hd']
  have hΦ₂ : biprod.map g (𝟙 C) ≫ Φ = g' := by
    apply biprod.hom_ext' <;> simp [Φ, ha'₂]
  have hΦ₃ : Φ ≫ h' = biprod.fst ≫ h := by
    have h0 : g' ≫ h' = 0 := comp_distTriang_mor_zero₂₃ _ hT'
    apply biprod.hom_ext' <;> simp [Φ, ha'₃, h0]
  have hΨΦ : Ψ ≫ Φ = 𝟙 _ := by
    have : IsIso (Ψ ≫ Φ) := by
      let φ : Triangle.mk (f ≫ biprod.inl) g' h' ⟶ Triangle.mk (f ≫ biprod.inl) g' h' :=
        Triangle.homMk _ _ (𝟙 _) (𝟙 _) (Ψ ≫ Φ) (by simp) (by simp [reassoc_of% hΨ₂, hΦ₂])
          (by
            change h' ≫ (𝟙 X)⟦(1 : ℤ)⟧' = (Ψ ≫ Φ) ≫ h'
            rw [Functor.map_id, comp_id, assoc, hΦ₃, biprod.lift_fst_assoc, hb₃])
      exact isIso₃_of_isIso₁₂ φ hT' hT' (inferInstanceAs (IsIso (𝟙 _)))
        (inferInstanceAs (IsIso (𝟙 _)))
    rw [← cancel_epi (Ψ ≫ Φ), comp_id, assoc, reassoc_of% hΦΨ]
  refine isomorphic_distinguished _ hT' _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ⟨Φ, Ψ, hΦΨ, hΨΦ⟩ (by simp) (by simpa using hΦ₂) (by simpa using hΦ₃.symm))


/-- The sum of a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` with the trivial triangle
`A ⟶ 0 ⟶ A⟦1⟧ ⟶ A⟦1⟧` is distinguished. -/
lemma mk_fst_comp_distinguished {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang D) (A : D) :
    Triangle.mk (biprod.fst ≫ f : X ⊞ A ⟶ Y) (g ≫ biprod.inl : Y ⟶ Z ⊞ A⟦(1 : ℤ)⟧)
      (biprod.desc (h ≫ (biprod.inl : X ⟶ X ⊞ A)⟦(1 : ℤ)⟧') (biprod.inr⟦(1 : ℤ)⟧')) ∈
      distTriang D := by
  rw [rotate_distinguished_triangle]
  let e : (X ⊞ A)⟦(1 : ℤ)⟧ ≅ X⟦(1 : ℤ)⟧ ⊞ A⟦(1 : ℤ)⟧ :=
    { hom := biprod.lift (biprod.fst⟦(1 : ℤ)⟧') (biprod.snd⟦(1 : ℤ)⟧')
      inv := biprod.desc (biprod.inl⟦(1 : ℤ)⟧') (biprod.inr⟦(1 : ℤ)⟧')
      hom_inv_id := by
        rw [biprod.lift_desc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add,
          biprod.total, Functor.map_id]
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [← Functor.map_comp] }
  refine isomorphic_distinguished _
    (mk_comp_inl_distinguished g h (-f⟦(1 : ℤ)⟧') (rot_of_distTriang _ hT) (A⟦(1 : ℤ)⟧)) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e (by simp) ?_ ?_)
  · change biprod.desc (h ≫ (biprod.inl : X ⟶ X ⊞ A)⟦(1 : ℤ)⟧') (biprod.inr⟦(1 : ℤ)⟧') ≫
      e.hom = 𝟙 _ ≫ biprod.map h (𝟙 _)
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [e, ← Functor.map_comp]
  · change (-(biprod.fst ≫ f)⟦(1 : ℤ)⟧') ≫ (𝟙 _)⟦(1 : ℤ)⟧' =
      e.hom ≫ biprod.fst ≫ (-f⟦(1 : ℤ)⟧')
    simp [e]

end Pretriangulated

namespace Triangulated

/-- Removing a summand `C` of the third object: an octahedron for `u₁₂` and
`u₂₃ ≫ inl : X₂ ⟶ X₃ ⊞ C`, with respect to the sums of the given triangles with the trivial
triangle `0 ⟶ C ⟶ C ⟶ 0`, gives an octahedron for `u₁₂` and `u₂₃`, provided the distinguished
triangles are stable under retracts. -/
lemma nonempty_octahedron_of_pad₃
    (hR : ∀ (T T' : Triangle D), T' ∈ distTriang D → Retract T T' → T ∈ distTriang D)
    {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : D} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
    {comm : u₁₂ ≫ u₂₃ = u₁₃}
    {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang D}
    {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang D}
    {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang D}
    (C : D)
    (H : Nonempty (Octahedron (u₂₃ := u₂₃ ≫ (biprod.inl : X₃ ⟶ X₃ ⊞ C))
      (u₁₃ := u₁₃ ≫ biprod.inl) (by rw [← comm, assoc]) h₁₂
      (mk_comp_inl_distinguished _ _ _ h₂₃ C) (mk_comp_inl_distinguished _ _ _ h₁₃ C))) :
    Nonempty (Octahedron comm h₁₂ h₂₃ h₁₃) := by
  obtain ⟨O⟩ := H
  have c₁ : v₁₂ ≫ O.m₁ = (u₂₃ ≫ biprod.inl) ≫ biprod.map v₁₃ (𝟙 C) := O.comm₁
  have c₂ : O.m₁ ≫ biprod.fst ≫ w₁₃ = w₁₂ := O.comm₂
  have c₃ : biprod.map v₁₃ (𝟙 C) ≫ O.m₃ = biprod.map v₂₃ (𝟙 C) := O.comm₃
  have c₄ : (biprod.fst ≫ w₁₃) ≫ u₁₂⟦(1 : ℤ)⟧' = O.m₃ ≫ biprod.fst ≫ w₂₃ := O.comm₄
  have hz : O.m₁ ≫ O.m₃ = 0 := comp_distTriang_mor_zero₁₂ _ O.mem
  have hr : biprod.inr ≫ O.m₃ = biprod.inr := by simpa using biprod.inr ≫= c₃
  let α : Z₁₃ ⟶ C := biprod.inl ≫ O.m₃ ≫ biprod.snd
  have hm₃ : O.m₃ ≫ biprod.snd = biprod.fst ≫ α + biprod.snd := by
    apply biprod.hom_ext' <;> simp [α, reassoc_of% hr]
  have hm₁ : O.m₁ ≫ biprod.snd = -(O.m₁ ≫ biprod.fst ≫ α) := by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← comp_add, ← hm₃, ← assoc, hz, zero_comp]
  have hm₃' : biprod.inl ≫ O.m₃ = (biprod.inl ≫ O.m₃ ≫ biprod.fst) ≫ biprod.inl +
      α ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp [α]
  have hmem : Triangle.mk (O.m₁ ≫ biprod.fst) (biprod.inl ≫ O.m₃ ≫ biprod.fst)
      (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧') ∈ distTriang D := by
    refine hR _ _ O.mem
      ⟨Triangle.homMk _ _ (𝟙 _) (biprod.inl - α ≫ biprod.inr) biprod.inl ?_ ?_ ?_,
        Triangle.homMk _ _ (𝟙 _) biprod.fst biprod.fst ?_ ?_ ?_, ?_⟩
    · change (O.m₁ ≫ biprod.fst) ≫ (biprod.inl - α ≫ biprod.inr) = 𝟙 _ ≫ O.m₁
      apply biprod.hom_ext <;> simp [hm₁]
    · change (biprod.inl ≫ O.m₃ ≫ biprod.fst) ≫ biprod.inl = (biprod.inl - α ≫ biprod.inr) ≫ O.m₃
      rw [sub_comp, hm₃', Category.assoc α biprod.inr O.m₃, hr]
      abel
    · change (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧') ≫ (𝟙 _)⟦(1 : ℤ)⟧' =
        biprod.inl ≫ (biprod.fst ≫ w₂₃) ≫ v₁₂⟦(1 : ℤ)⟧'
      simp
    · change O.m₁ ≫ biprod.fst = 𝟙 _ ≫ O.m₁ ≫ biprod.fst
      simp
    · change O.m₃ ≫ biprod.fst = biprod.fst ≫ biprod.inl ≫ O.m₃ ≫ biprod.fst
      apply biprod.hom_ext' <;> simp [reassoc_of% hr]
    · change ((biprod.fst ≫ w₂₃) ≫ v₁₂⟦(1 : ℤ)⟧') ≫ (𝟙 _)⟦(1 : ℤ)⟧' =
        biprod.fst ≫ w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧'
      simp
    · ext
      · simp
      · change (biprod.inl - α ≫ biprod.inr) ≫ biprod.fst = 𝟙 Z₁₃
        rw [sub_comp, biprod.inl_fst, assoc, biprod.inr_fst, comp_zero, sub_zero]
      · change biprod.inl ≫ biprod.fst = 𝟙 _
        simp
  exact ⟨{ m₁ := O.m₁ ≫ biprod.fst
           m₃ := biprod.inl ≫ O.m₃ ≫ biprod.fst
           comm₁ := by simpa using c₁ =≫ biprod.fst
           comm₂ := by simpa using c₂
           comm₃ := by simpa using biprod.inl ≫= c₃ =≫ biprod.fst
           comm₄ := by simpa using biprod.inl ≫= c₄
           mem := hmem }⟩

private lemma desc_shift_fst {X Z A : D} (w : Z ⟶ X⟦(1 : ℤ)⟧) :
    biprod.desc (w ≫ (biprod.inl : X ⟶ X ⊞ A)⟦(1 : ℤ)⟧') (biprod.inr⟦(1 : ℤ)⟧') ≫
      (biprod.fst : X ⊞ A ⟶ X)⟦(1 : ℤ)⟧' = biprod.fst ≫ w := by
  apply biprod.hom_ext' <;> simp [← Functor.map_comp]

private lemma desc_shift_snd {X Z A : D} (w : Z ⟶ X⟦(1 : ℤ)⟧) :
    biprod.desc (w ≫ (biprod.inl : X ⟶ X ⊞ A)⟦(1 : ℤ)⟧') (biprod.inr⟦(1 : ℤ)⟧') ≫
      (biprod.snd : X ⊞ A ⟶ A)⟦(1 : ℤ)⟧' = biprod.snd := by
  apply biprod.hom_ext' <;> simp [← Functor.map_comp]

/-- Removing a summand `B` of the second object: an octahedron for `u₁₂ ≫ inl : X₁ ⟶ X₂ ⊞ B`
and `fst ≫ u₂₃`, with respect to the sums of the given triangles with the trivial triangles
`0 ⟶ B ⟶ B ⟶ 0` and `B ⟶ 0 ⟶ B⟦1⟧ ⟶ B⟦1⟧`, gives an octahedron for `u₁₂` and `u₂₃`, provided
the distinguished triangles are stable under retracts. -/
lemma nonempty_octahedron_of_pad₂
    (hR : ∀ (T T' : Triangle D), T' ∈ distTriang D → Retract T T' → T ∈ distTriang D)
    {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : D} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
    {comm : u₁₂ ≫ u₂₃ = u₁₃}
    {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang D}
    {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang D}
    {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang D}
    (B : D)
    (H : Nonempty (Octahedron (u₁₂ := u₁₂ ≫ (biprod.inl : X₂ ⟶ X₂ ⊞ B))
      (u₂₃ := biprod.fst ≫ u₂₃) (by simp [comm])
      (mk_comp_inl_distinguished _ _ _ h₁₂ B) (mk_fst_comp_distinguished _ _ _ h₂₃ B) h₁₃)) :
    Nonempty (Octahedron comm h₁₂ h₂₃ h₁₃) := by
  obtain ⟨O⟩ := H
  have c₁ : biprod.map v₁₂ (𝟙 B) ≫ O.m₁ = (biprod.fst ≫ u₂₃) ≫ v₁₃ := O.comm₁
  have c₂ : O.m₁ ≫ w₁₃ = biprod.fst ≫ w₁₂ := O.comm₂
  have c₃ : v₁₃ ≫ O.m₃ = v₂₃ ≫ biprod.inl := O.comm₃
  have c₄ : w₁₃ ≫ (u₁₂ ≫ biprod.inl)⟦(1 : ℤ)⟧' = O.m₃ ≫
      biprod.desc (w₂₃ ≫ (biprod.inl : X₂ ⟶ X₂ ⊞ B)⟦(1 : ℤ)⟧') (biprod.inr⟦(1 : ℤ)⟧') := O.comm₄
  have hinr : biprod.inr ≫ O.m₁ = 0 := by simpa using biprod.inr ≫= c₁
  have hsnd : O.m₃ ≫ biprod.snd = 0 := by
    have := c₄ =≫ (biprod.snd : X₂ ⊞ B ⟶ B)⟦(1 : ℤ)⟧'
    rw [Category.assoc O.m₃, desc_shift_snd, Category.assoc w₁₃, ← Functor.map_comp, assoc,
      biprod.inl_snd, comp_zero,      Functor.map_zero, comp_zero] at this
    exact this.symm
  have hmem : Triangle.mk (biprod.inl ≫ O.m₁) (O.m₃ ≫ biprod.fst)
      (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧') ∈ distTriang D := by
    refine hR _ _ O.mem
      ⟨Triangle.homMk _ _ biprod.inl (𝟙 _) biprod.inl ?_ ?_ ?_,
        Triangle.homMk _ _ biprod.fst (𝟙 _) biprod.fst ?_ ?_ ?_, ?_⟩
    · change (biprod.inl ≫ O.m₁) ≫ 𝟙 _ = biprod.inl ≫ O.m₁
      simp
    · change (O.m₃ ≫ biprod.fst) ≫ biprod.inl = 𝟙 _ ≫ O.m₃
      apply biprod.hom_ext <;> simp [hsnd]
    · change (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧') ≫ (biprod.inl : Z₁₂ ⟶ Z₁₂ ⊞ B)⟦(1 : ℤ)⟧' = biprod.inl ≫
        biprod.desc (w₂₃ ≫ (biprod.inl : X₂ ⟶ X₂ ⊞ B)⟦(1 : ℤ)⟧') (biprod.inr⟦(1 : ℤ)⟧') ≫
          (biprod.map v₁₂ (𝟙 B))⟦(1 : ℤ)⟧'
      simp [← Functor.map_comp]
    · change O.m₁ ≫ 𝟙 _ = biprod.fst ≫ biprod.inl ≫ O.m₁
      apply biprod.hom_ext' <;> simp [hinr]
    · change O.m₃ ≫ biprod.fst = 𝟙 _ ≫ O.m₃ ≫ biprod.fst
      simp
    · change (biprod.desc (w₂₃ ≫ (biprod.inl : X₂ ⟶ X₂ ⊞ B)⟦(1 : ℤ)⟧') (biprod.inr⟦(1 : ℤ)⟧') ≫
          (biprod.map v₁₂ (𝟙 B))⟦(1 : ℤ)⟧') ≫ (biprod.fst : Z₁₂ ⊞ B ⟶ Z₁₂)⟦(1 : ℤ)⟧' =
        biprod.fst ≫ w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧'
      rw [assoc, ← Functor.map_comp, biprod.map_fst, Functor.map_comp, ← assoc,
        desc_shift_fst, assoc]
    · ext
      · change biprod.inl ≫ biprod.fst = 𝟙 Z₁₂
        simp
      · simp
      · change biprod.inl ≫ biprod.fst = 𝟙 Z₂₃
        simp
  exact ⟨{ m₁ := biprod.inl ≫ O.m₁
           m₃ := O.m₃ ≫ biprod.fst
           comm₁ := by simpa using biprod.inl ≫= c₁
           comm₂ := by simpa using biprod.inl ≫= c₂
           comm₃ := by simpa using c₃ =≫ biprod.fst
           comm₄ := by
             have := c₄ =≫ (biprod.fst : X₂ ⊞ B ⟶ X₂)⟦(1 : ℤ)⟧'
             rwa [Category.assoc O.m₃, desc_shift_fst, Category.assoc w₁₃, ← Functor.map_comp,
               assoc, biprod.inl_fst, comp_id, ← assoc] at this
           mem := hmem }⟩

/-- Removing a summand `A` of the first object: an octahedron for `fst ≫ u₁₂ : X₁ ⊞ A ⟶ X₂`
and `u₂₃`, with respect to the sums of the given triangles with the trivial triangle
`A ⟶ 0 ⟶ A⟦1⟧ ⟶ A⟦1⟧`, gives an octahedron for `u₁₂` and `u₂₃`, provided the distinguished
triangles are stable under retracts. -/
lemma nonempty_octahedron_of_pad₁
    (hR : ∀ (T T' : Triangle D), T' ∈ distTriang D → Retract T T' → T ∈ distTriang D)
    {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : D} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
    {comm : u₁₂ ≫ u₂₃ = u₁₃}
    {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang D}
    {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang D}
    {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang D}
    (A : D)
    (H : Nonempty (Octahedron (u₁₂ := (biprod.fst : X₁ ⊞ A ⟶ X₁) ≫ u₁₂)
      (u₁₃ := biprod.fst ≫ u₁₃) (by rw [assoc, comm])
      (mk_fst_comp_distinguished _ _ _ h₁₂ A) h₂₃ (mk_fst_comp_distinguished _ _ _ h₁₃ A))) :
    Nonempty (Octahedron comm h₁₂ h₂₃ h₁₃) := by
  obtain ⟨O⟩ := H
  have c₁ : (v₁₂ ≫ biprod.inl) ≫ O.m₁ = u₂₃ ≫ v₁₃ ≫ biprod.inl := O.comm₁
  have c₂ : O.m₁ ≫ biprod.desc (w₁₃ ≫ (biprod.inl : X₁ ⟶ X₁ ⊞ A)⟦(1 : ℤ)⟧')
      (biprod.inr⟦(1 : ℤ)⟧') =
      biprod.desc (w₁₂ ≫ (biprod.inl : X₁ ⟶ X₁ ⊞ A)⟦(1 : ℤ)⟧') (biprod.inr⟦(1 : ℤ)⟧') := O.comm₂
  have c₃ : (v₁₃ ≫ biprod.inl) ≫ O.m₃ = v₂₃ := O.comm₃
  have c₄ : biprod.desc (w₁₃ ≫ (biprod.inl : X₁ ⟶ X₁ ⊞ A)⟦(1 : ℤ)⟧') (biprod.inr⟦(1 : ℤ)⟧') ≫
      (biprod.fst ≫ u₁₂)⟦(1 : ℤ)⟧' = O.m₃ ≫ w₂₃ := O.comm₄
  have hz : O.m₁ ≫ O.m₃ = 0 := comp_distTriang_mor_zero₁₂ _ O.mem
  have hsnd : O.m₁ ≫ biprod.snd = biprod.snd := by
    have := c₂ =≫ (biprod.snd : X₁ ⊞ A ⟶ A)⟦(1 : ℤ)⟧'
    rwa [assoc, desc_shift_snd, desc_shift_snd] at this
  have hfst : O.m₁ ≫ biprod.fst ≫ w₁₃ = biprod.fst ≫ w₁₂ := by
    have := c₂ =≫ (biprod.fst : X₁ ⊞ A ⟶ X₁)⟦(1 : ℤ)⟧'
    rwa [assoc, desc_shift_fst, desc_shift_fst] at this
  let ψ := biprod.inr ≫ O.m₁ ≫ biprod.fst
  have hdec : O.m₁ = O.m₁ ≫ biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp [hsnd]
  have hinr : biprod.inr ≫ O.m₃ = -(ψ ≫ biprod.inl ≫ O.m₃) := by
    have := biprod.inr ≫= hz
    rw [hdec] at this
    simp only [add_comp, assoc, comp_add, biprod.inr_snd_assoc, comp_zero] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]
    simpa [ψ] using this
  have hmem : Triangle.mk (biprod.inl ≫ O.m₁ ≫ biprod.fst) (biprod.inl ≫ O.m₃)
      (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧') ∈ distTriang D := by
    refine hR _ _ O.mem
      ⟨Triangle.homMk _ _ biprod.inl biprod.inl (𝟙 _) ?_ ?_ ?_,
        Triangle.homMk _ _ biprod.fst (biprod.fst - biprod.snd ≫ ψ) (𝟙 _) ?_ ?_ ?_, ?_⟩
    · change (biprod.inl ≫ O.m₁ ≫ biprod.fst) ≫ biprod.inl = biprod.inl ≫ O.m₁
      apply biprod.hom_ext <;> simp [hsnd]
    · change (biprod.inl ≫ O.m₃) ≫ 𝟙 _ = biprod.inl ≫ O.m₃
      simp
    · change (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧') ≫ (biprod.inl : Z₁₂ ⟶ Z₁₂ ⊞ A⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧' =
        𝟙 _ ≫ w₂₃ ≫ (v₁₂ ≫ biprod.inl)⟦(1 : ℤ)⟧'
      simp
    · change O.m₁ ≫ (biprod.fst - biprod.snd ≫ ψ) = biprod.fst ≫ biprod.inl ≫ O.m₁ ≫ biprod.fst
      apply biprod.hom_ext' <;> simp [reassoc_of% hsnd, ψ]
    · change O.m₃ ≫ 𝟙 _ = (biprod.fst - biprod.snd ≫ ψ) ≫ biprod.inl ≫ O.m₃
      apply biprod.hom_ext' <;> simp [hinr]
    · change (w₂₃ ≫ (v₁₂ ≫ biprod.inl)⟦(1 : ℤ)⟧') ≫
        (biprod.fst : Z₁₂ ⊞ A⟦(1 : ℤ)⟧ ⟶ Z₁₂)⟦(1 : ℤ)⟧' = 𝟙 _ ≫ w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧'
      simp [← Functor.map_comp]
    · ext
      · change biprod.inl ≫ biprod.fst = 𝟙 Z₁₂
        simp
      · change biprod.inl ≫ (biprod.fst - biprod.snd ≫ ψ) = 𝟙 Z₁₃
        simp
      · simp
  exact ⟨{ m₁ := biprod.inl ≫ O.m₁ ≫ biprod.fst
           m₃ := biprod.inl ≫ O.m₃
           comm₁ := by simpa using c₁ =≫ biprod.fst
           comm₂ := by simpa using biprod.inl ≫= hfst
           comm₃ := by simpa using c₃
           comm₄ := by simpa [← Functor.map_comp] using biprod.inl ≫= c₄
           mem := hmem }⟩

end Triangulated

end CategoryTheory
