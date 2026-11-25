/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Mates of squares whose vertical functors are finite biproduct powers

For a preadditive category `C` with finite biproducts and `d : ℕ`, the *biproduct power*
`Functor.finBiproductPow C d : C ⥤ C` sends `c` to `⨁ (fun _ : Fin d ↦ c)`.

## Main results

* `Adjunction.isIso_mateEquiv_of_biproductPow_π`: let `G ⊣ R` with `R` additive, and let
  `α : V ⋙ G ⟶ G ⋙ V'` be a square whose vertical functors are identified with biproduct powers
  by `e : V ≅ finBiproductPow C d` and `e' : V' ≅ finBiproductPow C' d`. If `α` is compatible with
  the biproduct projections (i.e. after transport along `e`, `e'` it is the canonical comparison
  `G (c ^ d) ≅ (G c) ^ d`), then the mate `R ⋙ V ⟶ V' ⋙ R` of `α` is an isomorphism.
  The square is
  ```
  C --G--> C'
  |        |
  V        V'
  v        v
  C --G--> C'
  ```
* `Adjunction.isIso_mateEquiv_inv_of_biproductPow`: for a square of adjunctions in which the
  monads `E₁ ⋙ Res₁` and `E₂ ⋙ Res₂` are biproduct powers compatibly with the coefficient
  comparison, the mate `R₁ ⋙ E₁ ⟶ E₂ ⋙ R₂` of the inverse of the comparison
  `α : L₁ ⋙ E₂ ⟶ E₁ ⋙ L₂` is an isomorphism.
* `Adjunction.isIso_mateEquiv_inv_of_isIso_biproductDesc_unit`: the same conclusion when the
  biproduct decompositions are built from the units and natural endomorphisms `μ₁ i`, `μ₂ i` of
  the identity functors intertwined by `L₂`; the compatibility is then automatic.

## Implementation notes

The compatibility hypotheses cannot be dropped: an arbitrary isomorphism
`finBiproductPow ⋙ G ≅ G ⋙ finBiproductPow` is a `d × d` matrix with entries in `End G`, and its
mate is the matrix of the conjugates of the entries, *without* transposition. Since conjugation
reverses composition, this matrix need not be invertible when `End G` is not commutative
(e.g. `G = ℍ ⊗ - : ℝ-Vect ⥤ ℍ-Mod`, `d = 2`, matrix `!![1, i; j, k]`).
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

section

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The biproduct power `c ↦ c ^ d = ⨁ (fun _ : Fin d ↦ c)`. -/
@[simps]
noncomputable def Functor.finBiproductPow (d : ℕ) : C ⥤ C where
  obj c := ⨁ fun _ : Fin d ↦ c
  map f := biproduct.map fun _ ↦ f

end

section

variable {C C' : Type*} [Category C] [Category C'] [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive C'] [HasFiniteBiproducts C']

omit [HasFiniteBiproducts C'] in
/-- For an additive functor `F`, the comparison map `F (⨁ f) ⟶ ⨁ (F ∘ f)` built from the images
of the biproduct projections is an isomorphism. -/
lemma Functor.isIso_biproduct_lift_map_π (F : C ⥤ C') [F.Additive] {d : ℕ}
    (f : Fin d → C) : IsIso (biproduct.lift fun i ↦ F.map (biproduct.π f i)) := by
  refine ⟨biproduct.desc fun i ↦ F.map (biproduct.ι f i), ?_, ?_⟩
  · rw [biproduct.lift_desc, ← F.map_id, ← biproduct.total, F.map_sum]
    simp only [F.map_comp]
  · ext i j
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, ← F.map_comp,
      biproduct.ι_π, Category.id_comp]
    split_ifs with h
    · subst h
      simp
    · simp

omit [HasFiniteBiproducts C] [HasFiniteBiproducts C'] in
/-- Morphisms out of the image `F (⨁ f)` of a biproduct under an additive functor `F` are
determined by their precompositions with the images of the biproduct inclusions. -/
lemma Functor.map_biproduct_hom_ext (F : C ⥤ C') [F.Additive] {J : Type} [Finite J]
    {f : J → C} [HasBiproduct f] {Z : C'} {g h : F.obj (⨁ f) ⟶ Z}
    (w : ∀ j, F.map (biproduct.ι f j) ≫ g = F.map (biproduct.ι f j) ≫ h) : g = h := by
  have := Fintype.ofFinite J
  rw [← Category.id_comp g, ← Category.id_comp h, ← F.map_id, ← biproduct.total, F.map_sum,
    Preadditive.sum_comp, Preadditive.sum_comp]
  simp only [F.map_comp, Category.assoc, w]

/-- If a square `α : V ⋙ G ⟶ G ⋙ V'` is compatible with the `i`-th biproduct projection of the
biproduct powers `V ≅ finBiproductPow C d` and `V' ≅ finBiproductPow C' d`, then so is its mate
`R ⋙ V ⟶ V' ⋙ R`. -/
lemma Adjunction.mateEquiv_app_comp_map_biproductPow_π {G : C ⥤ C'} {R : C' ⥤ C} (adj : G ⊣ R)
    {d : ℕ} {V : C ⥤ C} {V' : C' ⥤ C'} (e : V ≅ Functor.finBiproductPow C d)
    (e' : V' ≅ Functor.finBiproductPow C' d) (α : TwoSquare V G G V') (i : Fin d)
    (hα : ∀ X : C, α.app X ≫ e'.hom.app (G.obj X) ≫ biproduct.π _ i =
      G.map (e.hom.app X ≫ biproduct.π _ i)) (Y : C') :
    (mateEquiv adj adj α).app Y ≫ R.map (e'.hom.app Y ≫ biproduct.π _ i) =
      e.hom.app (R.obj Y) ≫ biproduct.π _ i := by
  have h := e'.hom.naturality (adj.counit.app Y)
  simp only [Functor.finBiproductPow_map] at h
  simp only [mateEquiv_apply, Functor.comp_obj, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id, Category.assoc]
  rw [← R.map_comp, ← R.map_comp, reassoc_of% h, biproduct.map_π,
    reassoc_of% (hα (R.obj Y)), R.map_comp, adj.unit_naturality_assoc,
    Adjunction.right_triangle_components, Category.comp_id]

/-- Let `G ⊣ R` with `R` additive and let `α : V ⋙ G ⟶ G ⋙ V'` be a square whose vertical
functors are biproduct powers via `e : V ≅ finBiproductPow C d` and
`e' : V' ≅ finBiproductPow C' d`. If `α` is compatible with the biproduct projections, then the
mate `R ⋙ V ⟶ V' ⋙ R` of `α` is an isomorphism. (Without the compatibility hypothesis this
fails, see the module docstring.) -/
theorem Adjunction.isIso_mateEquiv_of_biproductPow_π {G : C ⥤ C'} {R : C' ⥤ C} [R.Additive]
    (adj : G ⊣ R) {d : ℕ} {V : C ⥤ C} {V' : C' ⥤ C'} (e : V ≅ Functor.finBiproductPow C d)
    (e' : V' ≅ Functor.finBiproductPow C' d) (α : TwoSquare V G G V')
    (hα : ∀ (X : C) (i : Fin d), α.app X ≫ e'.hom.app (G.obj X) ≫ biproduct.π _ i =
      G.map (e.hom.app X ≫ biproduct.π _ i)) :
    IsIso (mateEquiv adj adj α) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  have hc := R.isIso_biproduct_lift_map_π fun _ : Fin d ↦ Y
  have h : (mateEquiv adj adj α).app Y ≫ R.map (e'.hom.app Y) ≫
      (biproduct.lift fun i ↦ R.map (biproduct.π (fun _ : Fin d ↦ Y) i)) = e.hom.app (R.obj Y) :=
    biproduct.hom_ext _ _ fun i ↦ by
      rw [Category.assoc, Category.assoc, biproduct.lift_π, ← R.map_comp]
      exact mateEquiv_app_comp_map_biproductPow_π adj e e' α i (hα · i) Y
  have : IsIso ((mateEquiv adj adj α).app Y ≫ R.map (e'.hom.app Y) ≫
      (biproduct.lift fun i ↦ R.map (biproduct.π (fun _ : Fin d ↦ Y) i))) := by
    rw [h]
    infer_instance
  have : IsIso (R.map (e'.hom.app Y) ≫
      biproduct.lift fun i ↦ R.map (biproduct.π (fun _ : Fin d ↦ Y) i)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hc
  exact IsIso.of_isIso_comp_right _
    (R.map (e'.hom.app Y) ≫ biproduct.lift fun i ↦ R.map (biproduct.π (fun _ : Fin d ↦ Y) i))

end

section

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  [Preadditive A] [HasFiniteBiproducts A] [Preadditive A'] [HasFiniteBiproducts A']
  {E₁ : A ⥤ B} {Res₁ : B ⥤ A} {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'}
  {L₁ : A ⥤ A'} {R₁ : A' ⥤ A} {L₂ : B ⥤ B'} {R₂ : B' ⥤ B}

/-- Consider a square of adjunctions `E₁ ⊣ Res₁`, `E₂ ⊣ Res₂` (horizontal) and `L₁ ⊣ R₁`,
`L₂ ⊣ R₂` (vertical), an isomorphism `e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁` and an isomorphism
`α : L₁ ⋙ E₂ ⟶ E₁ ⋙ L₂` whose mate is `e.inv`. Suppose `R₁` is additive, `Res₁` reflects
isomorphisms, and the monads `E₁ ⋙ Res₁`, `E₂ ⋙ Res₂` are biproduct powers via `u₁`, `u₂` such
that the pasted square `(E₁ ⋙ Res₁) ⋙ L₁ ⟶ L₁ ⋙ (E₂ ⋙ Res₂)` (built from `e.inv` and `α⁻¹`) is
compatible with the biproduct projections. Then the mate `R₁ ⋙ E₁ ⟶ E₂ ⋙ R₂` of `α⁻¹` is an
isomorphism. -/
theorem Adjunction.isIso_mateEquiv_inv_of_biproductPow (adj₁ : E₁ ⊣ Res₁) (adj₂ : E₂ ⊣ Res₂)
    (adjL₁ : L₁ ⊣ R₁) (adjL₂ : L₂ ⊣ R₂) [R₁.Additive] [Res₁.ReflectsIsomorphisms]
    (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁) (α : TwoSquare L₁ E₁ E₂ L₂)
    (hα : mateEquiv adj₁ adj₂ α = TwoSquare.mk _ _ _ _ e.inv) [IsIso α]
    {d : ℕ} (u₁ : E₁ ⋙ Res₁ ≅ Functor.finBiproductPow A d)
    (u₂ : E₂ ⋙ Res₂ ≅ Functor.finBiproductPow A' d)
    (hu : ∀ (X : A) (i : Fin d), e.inv.app (E₁.obj X) ≫ Res₂.map (inv (α.app X)) ≫
      u₂.hom.app (L₁.obj X) ≫ biproduct.π _ i = L₁.map (u₁.hom.app X ≫ biproduct.π _ i)) :
    IsIso (mateEquiv adjL₁ adjL₂ (TwoSquare.mk _ _ _ _ (inv α))) := by
  have hU := isIso_mateEquiv_of_biproductPow_π adjL₁ u₁ u₂
    ((TwoSquare.mk _ _ _ _ (inv α)).hComp (TwoSquare.mk _ _ _ _ e.inv)) (fun X i ↦ by
      simpa [TwoSquare.hComp] using hu X i)
  rw [mateEquiv_vcomp adjL₁ adjL₂ adjL₁] at hU
  have hc : IsIso (mateEquiv adjL₂ adjL₁ (TwoSquare.mk _ _ _ _ e.inv)) := by
    rw [← hα, iterated_mateEquiv_conjugateEquiv]
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app] at hU ⊢
  intro M
  have hM := hU M
  simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id] at hM
  rw [← isIso_iff_of_reflects_iso _ Res₁]
  exact IsIso.of_isIso_comp_right _
    ((mateEquiv adjL₂ adjL₁ (TwoSquare.mk _ _ _ _ e.inv)).app (E₂.obj M))

/-- Given an adjunction `E ⊣ Res` and natural endomorphisms `μ i` (`i : Fin d`) of the identity
of `B`, the natural transformation `finBiproductPow A d ⟶ E ⋙ Res` whose `i`-th component is
`η ≫ Res (μ i)`. (For `μ i` the multiplication by the `i`-th element of a basis, this is the
map `M ^ d → Res (F ⊗ M)` sending `(mᵢ)` to `∑ bᵢ ⊗ mᵢ`.) -/
@[simps]
noncomputable def Adjunction.biproductDescUnit (adj : E₁ ⊣ Res₁) {d : ℕ}
    (μ : Fin d → (𝟭 B ⟶ 𝟭 B)) : Functor.finBiproductPow A d ⟶ E₁ ⋙ Res₁ where
  app X := biproduct.desc fun i ↦ adj.unit.app X ≫ Res₁.map ((μ i).app (E₁.obj X))
  naturality X Y f := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    have h := (μ i).naturality (E₁.map f)
    simp only [Functor.id_obj, Functor.id_map] at h
    simp only [Functor.comp_obj, Functor.finBiproductPow_map, biproduct.ι_map_assoc,
      biproduct.ι_desc, Category.assoc, Functor.comp_map, biproduct.ι_desc_assoc]
    rw [← adj.unit_naturality_assoc, ← Res₁.map_comp, ← Res₁.map_comp, h]

omit [Preadditive A] [HasFiniteBiproducts A] [Preadditive A'] [HasFiniteBiproducts A'] in
/-- In the setting of `Adjunction.isIso_mateEquiv_inv_of_biproductPow`, the pasted square
`(E₁ ⋙ Res₁) ⋙ L₁ ⟶ L₁ ⋙ (E₂ ⋙ Res₂)` built from `e.inv` and `α⁻¹` sends the map
`L₁ (η₁ ≫ Res₁ (μ₁ i))` to `η₂ ≫ Res₂ (μ₂ i)`, provided `L₂` intertwines `μ₁ i` and `μ₂ i`. -/
@[reassoc]
lemma Adjunction.map_unit_comp_mateEquiv_inv (adj₁ : E₁ ⊣ Res₁) (adj₂ : E₂ ⊣ Res₂)
    (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁) (α : TwoSquare L₁ E₁ E₂ L₂)
    (hα : mateEquiv adj₁ adj₂ α = TwoSquare.mk _ _ _ _ e.inv) [IsIso α]
    (μ₁ : 𝟭 B ⟶ 𝟭 B) (μ₂ : 𝟭 B' ⟶ 𝟭 B') (hμ : ∀ K : B, L₂.map (μ₁.app K) = μ₂.app (L₂.obj K))
    (X : A) :
    L₁.map (adj₁.unit.app X ≫ Res₁.map (μ₁.app (E₁.obj X))) ≫ e.inv.app (E₁.obj X) ≫
      Res₂.map (inv (α.app X)) =
      adj₂.unit.app (L₁.obj X) ≫ Res₂.map (μ₂.app (E₂.obj (L₁.obj X))) := by
  have hunit : L₁.map (adj₁.unit.app X) ≫ e.inv.app (E₁.obj X) =
      adj₂.unit.app (L₁.obj X) ≫ Res₂.map (α.app X) := by
    simpa [hα] using unit_mateEquiv adj₁ adj₂ α X
  have hnat := μ₂.naturality (inv (α.app X))
  have he := e.inv.naturality (μ₁.app (E₁.obj X))
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hnat he
  rw [L₁.map_comp, Category.assoc, reassoc_of% he, hμ, ← Res₂.map_comp, ← hnat, Res₂.map_comp,
    reassoc_of% hunit]
  simp


/-- A variant of `Adjunction.isIso_mateEquiv_inv_of_biproductPow` in which the biproduct
decompositions of the monads `E₁ ⋙ Res₁` and `E₂ ⋙ Res₂` are given by the maps
`η ≫ Res (μ i)` for natural endomorphisms `μ₁ i`, `μ₂ i` of the identity functors which are
intertwined by `L₂`. (For instance, `μ i` is the multiplication by the `i`-th element `bᵢ` of a
basis of a finite extension of coefficient rings, and `η ≫ Res (μ i)` is `m ↦ bᵢ ⊗ m`.) In this
case the compatibility of the decompositions with the pasted square is automatic. -/
theorem Adjunction.isIso_mateEquiv_inv_of_isIso_biproductDesc_unit (adj₁ : E₁ ⊣ Res₁)
    (adj₂ : E₂ ⊣ Res₂) (adjL₁ : L₁ ⊣ R₁) (adjL₂ : L₂ ⊣ R₂) [R₁.Additive]
    [Res₁.ReflectsIsomorphisms] (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁) (α : TwoSquare L₁ E₁ E₂ L₂)
    (hα : mateEquiv adj₁ adj₂ α = TwoSquare.mk _ _ _ _ e.inv) [IsIso α]
    {d : ℕ} (μ₁ : Fin d → (𝟭 B ⟶ 𝟭 B)) (μ₂ : Fin d → (𝟭 B' ⟶ 𝟭 B'))
    (hμ : ∀ i (K : B), L₂.map ((μ₁ i).app K) = (μ₂ i).app (L₂.obj K))
    (h₁ : ∀ X : A, IsIso (biproduct.desc fun i : Fin d ↦
      adj₁.unit.app X ≫ Res₁.map ((μ₁ i).app (E₁.obj X))))
    (h₂ : ∀ X : A', IsIso (biproduct.desc fun i : Fin d ↦
      adj₂.unit.app X ≫ Res₂.map ((μ₂ i).app (E₂.obj X)))) :
    IsIso (mateEquiv adjL₁ adjL₂ (TwoSquare.mk _ _ _ _ (inv α))) := by
  have := adjL₁.left_adjoint_additive
  have : IsIso (adj₁.biproductDescUnit μ₁) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact h₁
  have : IsIso (adj₂.biproductDescUnit μ₂) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact h₂
  refine isIso_mateEquiv_inv_of_biproductPow adj₁ adj₂ adjL₁ adjL₂ e α hα
    (asIso (adj₁.biproductDescUnit μ₁)).symm (asIso (adj₂.biproductDescUnit μ₂)).symm
    fun X i ↦ ?_
  rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv, NatIso.isIso_inv_app,
    NatIso.isIso_inv_app, ← cancel_epi (L₁.map ((adj₁.biproductDescUnit μ₁).app X)),
    ← L₁.map_comp, IsIso.hom_inv_id_assoc]
  refine L₁.map_biproduct_hom_ext fun j ↦ ?_
  rw [← L₁.map_comp_assoc, biproductDescUnit_app, biproduct.ι_desc,
    map_unit_comp_mateEquiv_inv_assoc adj₁ adj₂ e α hα (μ₁ j) (μ₂ j) (hμ j), ← L₁.map_comp,
    ← Category.assoc, ← biproduct.ι_desc (f := fun _ ↦ L₁.obj X) (fun j ↦ adj₂.unit.app _ ≫
      Res₂.map ((μ₂ j).app (E₂.obj (L₁.obj X)))) j, Category.assoc,
    ← biproductDescUnit_app adj₂ μ₂, IsIso.hom_inv_id_assoc, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h
  · subst h
    simp
  · simp

end

end CategoryTheory
