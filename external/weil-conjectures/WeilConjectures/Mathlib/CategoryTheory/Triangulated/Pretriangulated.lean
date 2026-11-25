/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Morphisms of distinguished triangles with a given middle component

Let `T = (X, Y, Z)` and `T' = (X', Y', Z')` be distinguished triangles in a pretriangulated
category. A morphism `φ : Y ⟶ Y'` with `X ⟶ Y ⟶ Y' ⟶ Z'` zero extends to a morphism of triangles
`T ⟶ T'`, and if `Hom(X⟦1⟧, Z') = 0` this extension is unique [BBD, 1.1.9].

## Main statements

- `CategoryTheory.Pretriangulated.exists_triangleHom_of_comp_eq_zero`: existence of the
  extension.
- `CategoryTheory.Pretriangulated.triangleHom_ext_of_subsingleton`: uniqueness of the
  extension.
- `CategoryTheory.Pretriangulated.exists_distTriang_counit_of_subsingleton`: the counit of an
  adjunction with fully faithful left adjoint completes to a distinguished triangle with the
  second map of a triangle whose first vertex is in the essential image and whose third vertex
  is right orthogonal to it.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

namespace Pretriangulated

namespace Triangle

variable {T : Triangle C} (hT : T ∈ distTriang C)
include hT

/-- If `Hom(X⟦1⟧, T.obj₃) = 0`, two maps `X ⟶ T.obj₁` with the same composite with `T.mor₁`
are equal. -/
lemma cancel_mor₁_of_subsingleton {X : C} [Subsingleton (X⟦(1 : ℤ)⟧ ⟶ T.obj₃)]
    {a a' : X ⟶ T.obj₁} (h : a ≫ T.mor₁ = a' ≫ T.mor₁) : a = a' := by
  rw [← sub_eq_zero]
  obtain ⟨g, hg⟩ := coyoneda_exact₁ T hT ((a - a')⟦(1 : ℤ)⟧')
    (by rw [← Functor.map_comp, Preadditive.sub_comp, h, sub_self, Functor.map_zero])
  rw [Subsingleton.elim g 0, zero_comp] at hg
  exact (CategoryTheory.shiftFunctor C (1 : ℤ)).map_eq_zero_iff.mp hg

/-- If `Hom(T.obj₁⟦1⟧, Y) = 0`, two maps `T.obj₃ ⟶ Y` with the same composite with `T.mor₂`
are equal. -/
lemma cancel_mor₂_of_subsingleton {Y : C} [Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ Y)]
    {c c' : T.obj₃ ⟶ Y} (h : T.mor₂ ≫ c = T.mor₂ ≫ c') : c = c' := by
  rw [← sub_eq_zero]
  obtain ⟨g, hg⟩ := yoneda_exact₃ T hT (c - c') (by rw [Preadditive.comp_sub, h, sub_self])
  rw [hg, Subsingleton.elim g 0, comp_zero]

omit hT in
include hT in
/-- An endomorphism `k` of the first object of a distinguished triangle which is killed by
`T.mor₁` and kills `T.mor₃` (up to shift) is of square zero. -/
lemma comp_self_eq_zero {k : T.obj₁ ⟶ T.obj₁} (h₁ : k ≫ T.mor₁ = 0)
    (h₃ : T.mor₃ ≫ k⟦(1 : ℤ)⟧' = 0) : k ≫ k = 0 := by
  obtain ⟨g, hg⟩ := coyoneda_exact₁ T hT (k⟦(1 : ℤ)⟧')
    (by rw [← Functor.map_comp, h₁, Functor.map_zero])
  obtain ⟨g', hg'⟩ := yoneda_exact₃ _ (rot_of_distTriang _ hT) (k⟦(1 : ℤ)⟧') h₃
  apply (CategoryTheory.shiftFunctor C (1 : ℤ)).map_injective
  rw [Functor.map_comp, Functor.map_zero]
  nth_rw 1 [hg]
  rw [hg', Triangle.rotate_mor₃]
  simp [comp_distTriang_mor_zero₃₁_assoc _ hT]

end Triangle

/-- Let `ψ : T ⟶ T'` be a morphism of distinguished triangles such that `T.mor₁ = 0` and
`ψ.hom₁ = 0`. Then there is a map `b : T.obj₃ ⟶ T'.obj₂` with `T.mor₂ ≫ b = ψ.hom₂` and
`b ≫ T'.mor₂ = ψ.hom₃`. -/
lemma exists_lift_of_mor₁_eq_zero {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (hT₁ : T.mor₁ = 0) (ψ : T ⟶ T') (hψ₁ : ψ.hom₁ = 0) :
    ∃ b : T.obj₃ ⟶ T'.obj₂, T.mor₂ ≫ b = ψ.hom₂ ∧ b ≫ T'.mor₂ = ψ.hom₃ := by
  obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ T hT ψ.hom₂ (by rw [hT₁, zero_comp])
  obtain ⟨y, hy⟩ := Triangle.yoneda_exact₃ T hT (r ≫ T'.mor₂ - ψ.hom₃) (by
    rw [Preadditive.comp_sub, reassoc_of% hr.symm, ψ.comm₂, sub_self])
  have : Epi T.mor₃ := (Triangle.mor₁_eq_zero_iff_epi₃ T hT).1 hT₁
  obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₃ T' hT' y (by
    rw [← cancel_epi T.mor₃, ← Category.assoc, ← hy, comp_zero, Preadditive.sub_comp,
      Category.assoc, comp_distTriang_mor_zero₂₃ _ hT', comp_zero, zero_sub, ← ψ.comm₃,
      hψ₁, Functor.map_zero, comp_zero, neg_zero])
  refine ⟨r - T.mor₃ ≫ z, ?_, ?_⟩
  · rw [Preadditive.comp_sub, ← hr, comp_distTriang_mor_zero₂₃_assoc _ hT, zero_comp, sub_zero]
  · rw [Preadditive.sub_comp, Category.assoc, ← hz, ← hy, sub_sub_cancel]

/-- Let `φ : T ⟶ T'` and `φ' : T' ⟶ T` be morphisms of distinguished triangles such that the
composites `φ ≫ φ'` and `φ' ≫ φ` act as the identity on `T.mor₁`, `T.mor₃` (resp. `T'.mor₁`,
`T'.mor₃`) through their second and third components. Then `φ.hom₁` is an isomorphism: the
endomorphisms `𝟙 - (φ ≫ φ').hom₁` and `𝟙 - (φ' ≫ φ).hom₁` are of square zero. -/
lemma isIso_hom₁_of_comp {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (φ : T ⟶ T') (φ' : T' ⟶ T)
    (h₂ : T.mor₁ ≫ φ.hom₂ ≫ φ'.hom₂ = T.mor₁) (h₃ : φ.hom₃ ≫ φ'.hom₃ ≫ T.mor₃ = T.mor₃)
    (h₂' : T'.mor₁ ≫ φ'.hom₂ ≫ φ.hom₂ = T'.mor₁)
    (h₃' : φ'.hom₃ ≫ φ.hom₃ ≫ T'.mor₃ = T'.mor₃) : IsIso φ.hom₁ := by
  have key : ∀ {T T' : Triangle C} (_ : T ∈ distTriang C) (φ : T ⟶ T') (φ' : T' ⟶ T)
      (_ : T.mor₁ ≫ φ.hom₂ ≫ φ'.hom₂ = T.mor₁) (_ : φ.hom₃ ≫ φ'.hom₃ ≫ T.mor₃ = T.mor₃),
      IsIso (φ.hom₁ ≫ φ'.hom₁) := by
    intro T T' hT φ φ' h₂ h₃
    have hk := Triangle.comp_self_eq_zero hT (k := 𝟙 _ - φ.hom₁ ≫ φ'.hom₁)
      (by
        rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, ← φ'.comm₁,
          ← φ.comm₁_assoc, h₂, sub_self])
      (by
        simp only [Functor.map_sub, Functor.map_id, Functor.map_comp, Preadditive.comp_sub,
          Category.comp_id]
        rw [φ.comm₃_assoc, φ'.comm₃, h₃, sub_self])
    set k := 𝟙 _ - φ.hom₁ ≫ φ'.hom₁
    have e : φ.hom₁ ≫ φ'.hom₁ = 𝟙 _ - k := by simp [k]
    rw [e]
    refine ⟨𝟙 _ + k, ?_, ?_⟩
    · simp only [Preadditive.sub_comp, Preadditive.comp_add, Category.id_comp,
        Category.comp_id, hk]
      abel
    · simp only [Preadditive.add_comp, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, hk]
      abel
  have := key hT φ φ' h₂ h₃
  have := key hT' φ' φ h₂' h₃'
  refine ⟨⟨φ'.hom₁ ≫ inv (φ.hom₁ ≫ φ'.hom₁),
    by rw [← Category.assoc, IsIso.hom_inv_id], ?_⟩⟩
  have e : inv (φ'.hom₁ ≫ φ.hom₁) ≫ φ'.hom₁ = φ'.hom₁ ≫ inv (φ.hom₁ ≫ φ'.hom₁) := by
    rw [← cancel_mono (φ.hom₁ ≫ φ'.hom₁), Category.assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, ← Category.assoc φ'.hom₁ φ.hom₁, IsIso.inv_hom_id_assoc]
  rw [← e, Category.assoc, IsIso.inv_hom_id]

/-- **Extension of a middle component** [BBD, 1.1.9]. Given distinguished triangles `T` and `T'`,
a morphism `φ : T.obj₂ ⟶ T'.obj₂` such that `T.mor₁ ≫ φ ≫ T'.mor₂ = 0` is the middle component of
a morphism of triangles `T ⟶ T'`. -/
theorem exists_triangleHom_of_comp_eq_zero {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (φ : T.obj₂ ⟶ T'.obj₂) (hφ : T.mor₁ ≫ φ ≫ T'.mor₂ = 0) :
    ∃ τ : T ⟶ T', τ.hom₂ = φ := by
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ T' hT' (T.mor₁ ≫ φ) (by simpa using hφ)
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism T T' hT hT' a φ ha
  exact ⟨{ hom₁ := a, hom₂ := φ, hom₃ := c, comm₁ := ha, comm₂ := hc₁, comm₃ := hc₂ }, rfl⟩

/-- **Uniqueness of the extension of a middle component** [BBD, 1.1.9]. Let `T` and `T'` be
distinguished triangles with `Hom(T.obj₁⟦1⟧, T'.obj₃) = 0`. Then a morphism of triangles
`T ⟶ T'` is determined by its middle component. -/
theorem triangleHom_ext_of_subsingleton {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) [Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃)] {τ τ' : T ⟶ T'}
    (h : τ.hom₂ = τ'.hom₂) : τ = τ' := by
  ext
  · exact Triangle.cancel_mor₁_of_subsingleton hT' (by rw [← τ.comm₁, ← τ'.comm₁, h])
  · exact h
  · exact Triangle.cancel_mor₂_of_subsingleton hT (by rw [τ.comm₂, τ'.comm₂, h])

/-- For a morphism `φ : T ⟶ T'` of distinguished triangles whose second objects vanish,
```
X  ⟶ 0 ⟶ Z  ⟶ X⟦1⟧
↓φ₁       ↓φ₃    ↓φ₁⟦1⟧
X' ⟶ 0 ⟶ Z' ⟶ X'⟦1⟧
```
the first component of `φ` vanishes if and only if the third one does: the third morphisms of
the triangles are isomorphisms, and they intertwine `φ.hom₃` with `φ.hom₁⟦1⟧'`. -/
lemma hom₁_eq_zero_iff_hom₃_eq_zero {T T' : Triangle C} (φ : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (h₂ : IsZero T.obj₂)
    (h₂' : IsZero T'.obj₂) : φ.hom₁ = 0 ↔ φ.hom₃ = 0 := by
  have := (T.isZero₂_iff_isIso₃ hT).1 h₂
  have := (T'.isZero₂_iff_isIso₃ hT').1 h₂'
  have hc := φ.comm₃
  constructor
  · intro h
    rw [h, Functor.map_zero, Limits.comp_zero] at hc
    rw [← cancel_mono T'.mor₃, ← hc, Limits.zero_comp]
  · intro h
    rw [h, Limits.zero_comp] at hc
    have : (CategoryTheory.shiftFunctor C (1 : ℤ)).map φ.hom₁ = 0 := by
      rw [← cancel_epi T.mor₃, hc, Limits.comp_zero]
    exact (CategoryTheory.shiftFunctor C (1 : ℤ)).map_injective (by rw [this, Functor.map_zero])

section Adjunction

variable {D : Type*} [Category* D]

/-- **Completing a counit by a triangle.** Let `F ⊣ G` with `F` fully faithful, and let
`K ⟶ L ⟶ R ⟶ K⟦1⟧` be a distinguished triangle whose first vertex `K` lies in the essential
image of `F` and whose third vertex receives no maps from the shifts of objects of that
essential image. Then the counit `F G L ⟶ L` and the second map `L ⟶ R` extend to a
distinguished triangle `F G L ⟶ L ⟶ R ⟶ (F G L)⟦1⟧`.

Indeed `F G L ⟶ L` factors through `K ⟶ L` by a map `b`, and composition with `b` is bijective on
maps out of the essential image of `F`: composition with `K ⟶ L` is bijective there, by the
long exact sequence of the triangle, and so is composition with the counit, by full faithfulness
of `F`. As both ends of `b` lie in the essential image, `b` is an isomorphism. -/
theorem exists_distTriang_counit_of_subsingleton {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    (hF : F.FullyFaithful) {T : Triangle C} (hT : T ∈ distTriang C)
    (h₃ : ∀ (M : D) (n : ℤ), Subsingleton ((F.obj M)⟦n⟧ ⟶ T.obj₃))
    (h₁ : F.essImage T.obj₁) :
    ∃ w, Triangle.mk (adj.counit.app T.obj₂) T.mor₂ w ∈ distTriang C := by
  have h₀ (M : D) : Subsingleton (F.obj M ⟶ T.obj₃) :=
    have := h₃ M 0
    ((shiftFunctorZero C ℤ).app (F.obj M)).homFromEquiv.symm.subsingleton
  obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ T hT (adj.counit.app T.obj₂)
    ((h₀ (G.obj T.obj₂)).elim _ _)
  -- composing with `T.mor₁` is bijective on maps out of the essential image
  have ha (M : D) : Function.Bijective (fun x : F.obj M ⟶ T.obj₁ ↦ x ≫ T.mor₁) := by
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
    · have := h₃ M 1
      exact Triangle.cancel_mor₁_of_subsingleton hT hxy
    · exact (Triangle.coyoneda_exact₂ T hT y ((h₀ M).elim _ _)).imp fun x hx ↦ hx.symm
  have hε (M : D) : Function.Bijective
      (fun x : F.obj M ⟶ F.obj (G.obj T.obj₂) ↦ x ≫ adj.counit.app T.obj₂) := by
    have : (fun x : F.obj M ⟶ F.obj (G.obj T.obj₂) ↦ x ≫ adj.counit.app T.obj₂) =
        (adj.homEquiv _ _).symm ∘ hF.preimage := by
      ext x
      simp [Adjunction.homEquiv_counit]
    rw [this]
    exact (adj.homEquiv _ _).symm.bijective.comp hF.homEquiv.symm.bijective
  have hb' (M : D) : Function.Bijective
      (fun x : F.obj M ⟶ F.obj (G.obj T.obj₂) ↦ x ≫ b) := by
    refine (Function.Bijective.of_comp_iff' (ha M) _).1 ?_
    have : ((fun x : F.obj M ⟶ T.obj₁ ↦ x ≫ T.mor₁) ∘
        fun x : F.obj M ⟶ F.obj (G.obj T.obj₂) ↦ x ≫ b) =
        fun x ↦ x ≫ adj.counit.app T.obj₂ := by
      funext x
      simp [hb]
    rw [this]
    exact hε M
  obtain ⟨N, ⟨e⟩⟩ := h₁
  obtain ⟨s, hs⟩ := (hb' N).2 e.hom
  have hsb : e.inv ≫ s ≫ b = 𝟙 _ := by simp [hs]
  have hbs : b ≫ e.inv ≫ s = 𝟙 _ :=
    (hb' (G.obj T.obj₂)).1 (by dsimp; rw [Category.assoc, Category.assoc, hsb]; simp)
  let eb : F.obj (G.obj T.obj₂) ≅ T.obj₁ := ⟨b, e.inv ≫ s, hbs, by rw [Category.assoc, hsb]⟩
  refine ⟨T.mor₃ ≫ eb.inv⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ eb (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change adj.counit.app T.obj₂ ≫ 𝟙 _ = b ≫ T.mor₁
    rw [hb, Category.comp_id]
  · change T.mor₂ ≫ 𝟙 _ = 𝟙 _ ≫ T.mor₂
    rw [Category.comp_id, Category.id_comp]
  · change (T.mor₃ ≫ eb.inv⟦(1 : ℤ)⟧') ≫ eb.hom⟦(1 : ℤ)⟧' = 𝟙 _ ≫ T.mor₃
    rw [Category.assoc, ← Functor.map_comp, eb.inv_hom_id, Functor.map_id, Category.comp_id,
      Category.id_comp]

end Adjunction

end Pretriangulated

end CategoryTheory

namespace CategoryTheory.Pretriangulated

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Pre-triangulated categories.** A pre-triangulated category (`Pretriangulated C`) is an
additive category with a shift `[1]` and a class of distinguished triangles satisfying (TR1)
distinguished triangles are closed under isomorphism, `X ⟶ X ⟶ 0 ⟶ X[1]` is distinguished and
every morphism is the first arrow of a distinguished triangle; (TR2) a triangle is distinguished
iff its rotation is; (TR3) a commutative square between the bases of two distinguished
triangles extends to a morphism of triangles. A triangulated category
(`CategoryTheory.IsTriangulated`) satisfies moreover the octahedral axiom, and an exact functor
is a functor commuting with the shift and preserving distinguished triangles
(`CategoryTheory.Functor.IsTriangulated`, see `Functor.isTriangulated_iff_map_distinguished`).
(blueprint: `def-weil-triangulated-category`) -/
theorem tr1_tr2_tr3 :
    (∀ T₁ T₂ : Triangle C, (T₁ ≅ T₂) → T₂ ∈ distTriang C → T₁ ∈ distTriang C) ∧
    (∀ X : C, contractibleTriangle X ∈ distTriang C) ∧
    (∀ {X Y : C} (u : X ⟶ Y), ∃ (Z : C) (v : Y ⟶ Z) (w : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk u v w ∈ distTriang C) ∧
    (∀ T : Triangle C, T ∈ distTriang C ↔ T.rotate ∈ distTriang C) ∧
    (∀ T₁ T₂ : Triangle C, T₁ ∈ distTriang C → T₂ ∈ distTriang C →
      ∀ (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂), T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
        ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
          T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃) :=
  ⟨fun _ _ e h ↦ isomorphic_distinguished _ h _ e, contractible_distinguished,
    fun u ↦ distinguished_cocone_triangle u, rotate_distinguished_triangle,
    fun _ _ h₁ h₂ a b w ↦ complete_distinguished_triangle_morphism _ _ h₁ h₂ a b w⟩


end CategoryTheory.Pretriangulated
