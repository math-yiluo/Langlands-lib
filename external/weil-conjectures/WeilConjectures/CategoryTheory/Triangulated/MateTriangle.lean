/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Mates of squares whose vertical functors are cones of a natural endomorphism

This is the triangulated analogue of `WeilConjectures.CategoryTheory.Adjunction.MateBiproduct`.
For the coefficient change `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, the monad `Res ∘ (- ⊗ᴸ 𝒪_E ⧸ ℓⁿ)` is not a
biproduct power but the cone of the multiplication by `ℓⁿ`: there is a natural distinguished
triangle `K --ℓⁿ--> K --η--> Res (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ) ⟶ K[1]`.

## Main results

* `Adjunction.isIso_mateEquiv_of_distTriang`: let `G ⊣ R` be an adjunction compatible with the
  shifts, with `R` triangulated, and let `α : V ⋙ G ⟶ G ⋙ V'` be a square whose vertical
  functors are cones of natural endomorphisms `a`, `a'` of the identity (natural distinguished
  triangles `X --a--> X --u--> V X --w--> X[1]`), with `R (a') = a`. If `α` is compatible with
  the second and third maps `u`, `w` of the triangles, then the mate `R ⋙ V ⟶ V' ⋙ R` of `α` is
  an isomorphism (five lemma).
* `Adjunction.isIso_mateEquiv_inv_of_distTriang`: for a square of adjunctions in which the
  monads `E₁ ⋙ Res₁` and `E₂ ⋙ Res₂` are such cones, with second map the unit, the mate
  `R₁ ⋙ E₁ ⟶ E₂ ⋙ R₂` of the inverse of the coefficient comparison `α : L₁ ⋙ E₂ ⟶ E₁ ⋙ L₂` is
  an isomorphism, provided `Res₁` reflects isomorphisms and the pasted square is compatible with
  the connecting maps (compatibility with the units is automatic).
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated

section Unit

variable {C C' : Type*} [Category* C] [Category* C'] {G : C ⥤ C'} {R : C' ⥤ C} (adj : G ⊣ R)
  {V : C ⥤ C} {V' : C' ⥤ C'} (u : 𝟭 C ⟶ V) (u' : 𝟭 C' ⟶ V') (α : TwoSquare V G G V')

/-- If a square `α : V ⋙ G ⟶ G ⋙ V'` is compatible with natural maps `u : 𝟭 ⟶ V`,
`u' : 𝟭 ⟶ V'`, then so is its mate `R ⋙ V ⟶ V' ⋙ R`. -/
@[reassoc]
lemma Adjunction.app_comp_mateEquiv_app_of_comm
    (hu : ∀ X : C, G.map (u.app X) ≫ α.app X = u'.app (G.obj X)) (Y : C') :
    u.app (R.obj Y) ≫ (mateEquiv adj adj α).app Y = R.map (u'.app Y) := by
  have h := u'.naturality (adj.counit.app Y)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj] at h
  simp only [mateEquiv_apply, Functor.comp_obj, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id]
  rw [← adj.unit_naturality_assoc, ← R.map_comp_assoc, hu, ← R.map_comp, ← h, R.map_comp,
    Adjunction.right_triangle_components_assoc]

end Unit

section Shift

variable {C C' : Type*} [Category* C] [Category* C'] [HasShift C ℤ] [HasShift C' ℤ]
  {G : C ⥤ C'} {R : C' ⥤ C} (adj : G ⊣ R) [G.CommShift ℤ] [R.CommShift ℤ] [adj.CommShift ℤ]
  {V : C ⥤ C} {V' : C' ⥤ C'} (w : V ⟶ shiftFunctor C (1 : ℤ))
  (w' : V' ⟶ shiftFunctor C' (1 : ℤ)) (α : TwoSquare V G G V')

/-- If a square `α : V ⋙ G ⟶ G ⋙ V'` is compatible with natural maps `w : V ⟶ [1]`,
`w' : V' ⟶ [1]` (through the commutation of `G` with the shift), then so is its mate
`R ⋙ V ⟶ V' ⋙ R`, for an adjunction `G ⊣ R` compatible with the shifts. -/
@[reassoc]
lemma Adjunction.mateEquiv_app_comp_of_comm
    (hw : ∀ X : C, α.app X ≫ w'.app (G.obj X) =
      G.map (w.app X) ≫ (G.commShiftIso (1 : ℤ)).hom.app X) (Y : C') :
    (mateEquiv adj adj α).app Y ≫ R.map (w'.app Y) ≫
      (R.commShiftIso (1 : ℤ)).hom.app Y = w.app (R.obj Y) := by
  have h := w'.naturality (adj.counit.app Y)
  have hc := (R.commShiftIso (1 : ℤ)).hom.naturality (adj.counit.app Y)
  have hu := adj.unit_app_commShiftIso_hom_app ℤ (1 : ℤ) (R.obj Y)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h hc
  rw [Functor.commShiftIso_comp_hom_app] at hu
  simp only [mateEquiv_apply, Functor.comp_obj, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id, Category.assoc]
  rw [← R.map_comp_assoc (V'.map _), h, R.map_comp_assoc,
    ← R.map_comp_assoc (α.app _), hw, hc,
    R.map_comp_assoc, adj.unit_naturality_assoc, reassoc_of% hu, ← Functor.map_comp,
    Adjunction.right_triangle_components, Functor.map_id, Category.comp_id]

end Shift

section Triangulated

variable {C C' : Type*} [Category* C] [Category* C'] [HasZeroObject C] [HasZeroObject C']
  [Preadditive C] [Preadditive C'] [HasShift C ℤ] [HasShift C' ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive]
  [Pretriangulated C] [Pretriangulated C']

/-- **Mates of squares between cones.** Let `G ⊣ R` be an adjunction compatible with the shifts,
with `R` triangulated, and let `V`, `V'` be endofunctors with natural distinguished triangles
`X --a--> X --u--> V X --w--> X[1]` and `Y --a'--> Y --u'--> V' Y --w'--> Y[1]`, where `a`, `a'`
are natural endomorphisms of the identity with `R (a') = a`. If a square
`α : V ⋙ G ⟶ G ⋙ V'` is compatible with `u`, `u'` and with `w`, `w'`, then its mate
`R ⋙ V ⟶ V' ⋙ R` is an isomorphism: at `Y` it is the third component of a morphism of
distinguished triangles whose first two components are identities. -/
theorem Adjunction.isIso_mateEquiv_of_distTriang {G : C ⥤ C'} {R : C' ⥤ C} (adj : G ⊣ R)
    [G.CommShift ℤ] [R.CommShift ℤ] [adj.CommShift ℤ] [R.IsTriangulated]
    {V : C ⥤ C} {V' : C' ⥤ C'} (a : 𝟭 C ⟶ 𝟭 C) (a' : 𝟭 C' ⟶ 𝟭 C')
    (u : 𝟭 C ⟶ V) (u' : 𝟭 C' ⟶ V')
    (w : V ⟶ shiftFunctor C (1 : ℤ)) (w' : V' ⟶ shiftFunctor C' (1 : ℤ))
    (hT : ∀ X : C, Triangle.mk (a.app X) (u.app X) (w.app X) ∈ distTriang C)
    (hT' : ∀ Y : C', Triangle.mk (a'.app Y) (u'.app Y) (w'.app Y) ∈ distTriang C')
    (ha : ∀ Y : C', R.map (a'.app Y) = a.app (R.obj Y)) (α : TwoSquare V G G V')
    (hu : ∀ X : C, G.map (u.app X) ≫ α.app X = u'.app (G.obj X))
    (hw : ∀ X : C, α.app X ≫ w'.app (G.obj X) =
      G.map (w.app X) ≫ (G.commShiftIso (1 : ℤ)).hom.app X) :
    IsIso (mateEquiv adj adj α) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  let φ : Triangle.mk (a.app (R.obj Y)) (u.app (R.obj Y)) (w.app (R.obj Y)) ⟶
      R.mapTriangle.obj (Triangle.mk (a'.app Y) (u'.app Y) (w'.app Y)) :=
    { hom₁ := 𝟙 _
      hom₂ := 𝟙 _
      hom₃ := (mateEquiv adj adj α).app Y
      comm₁ := by simp [Functor.mapTriangle, ha]
      comm₂ := by simpa [Functor.mapTriangle] using adj.app_comp_mateEquiv_app_of_comm u u' α hu Y
      comm₃ := by
        dsimp [Functor.mapTriangle]
        simp only [Functor.map_id, comp_id]
        exact (adj.mateEquiv_app_comp_of_comm w w' α hw Y).symm }
  exact isIso₃_of_isIso₁₂ φ (hT _) (R.map_distinguished _ (hT' Y))
    (inferInstanceAs (IsIso (𝟙 _)))
    (inferInstanceAs (IsIso (𝟙 _)))

variable {B B' : Type*} [Category* B] [Category* B']

/-- **Mates of coefficient comparisons whose monads are cones.** Consider a square of adjunctions
`E₁ ⊣ Res₁`, `E₂ ⊣ Res₂` (horizontal, the coefficient changes and their restrictions of scalars)
and `L₁ ⊣ R₁`, `L₂ ⊣ R₂` (vertical), an isomorphism `e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁` and an
isomorphism `α : L₁ ⋙ E₂ ⟶ E₁ ⋙ L₂` whose mate is `e.inv`. Suppose `L₁ ⊣ R₁` is compatible with
the shifts, `R₁` is triangulated, `Res₁` reflects isomorphisms, and the monads `E₁ ⋙ Res₁`,
`E₂ ⋙ Res₂` are cones of natural endomorphisms `a`, `a'` of the identity with `R₁ (a') = a`,
through natural distinguished triangles `X --a--> X --η--> Res (E X) --w--> X[1]` whose second
map is the unit. If the pasted square `(E₁ ⋙ Res₁) ⋙ L₁ ⟶ L₁ ⋙ (E₂ ⋙ Res₂)` (built from `e.inv`
and `α⁻¹`) is compatible with the connecting maps `w₁`, `w₂`, then the mate
`R₁ ⋙ E₁ ⟶ E₂ ⋙ R₂` of `α⁻¹` is an isomorphism.

This is the analogue of `Adjunction.isIso_mateEquiv_inv_of_biproductPow` for the coefficient
change `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, where `Res (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ)` is the cone of `ℓⁿ : K ⟶ K`. -/
theorem Adjunction.isIso_mateEquiv_inv_of_distTriang
    {E₁ : C ⥤ B} {Res₁ : B ⥤ C} {E₂ : C' ⥤ B'} {Res₂ : B' ⥤ C'}
    {L₁ : C ⥤ C'} {R₁ : C' ⥤ C} {L₂ : B ⥤ B'} {R₂ : B' ⥤ B}
    (adj₁ : E₁ ⊣ Res₁) (adj₂ : E₂ ⊣ Res₂) (adjL₁ : L₁ ⊣ R₁) (adjL₂ : L₂ ⊣ R₂)
    [L₁.CommShift ℤ] [R₁.CommShift ℤ] [adjL₁.CommShift ℤ] [R₁.IsTriangulated]
    [Res₁.ReflectsIsomorphisms]
    (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁) (α : TwoSquare L₁ E₁ E₂ L₂)
    (hα : mateEquiv adj₁ adj₂ α = TwoSquare.mk _ _ _ _ e.inv) [IsIso α]
    (a : 𝟭 C ⟶ 𝟭 C) (a' : 𝟭 C' ⟶ 𝟭 C')
    (w₁ : E₁ ⋙ Res₁ ⟶ shiftFunctor C (1 : ℤ)) (w₂ : E₂ ⋙ Res₂ ⟶ shiftFunctor C' (1 : ℤ))
    (hT₁ : ∀ X : C, Triangle.mk (a.app X) (adj₁.unit.app X) (w₁.app X) ∈ distTriang C)
    (hT₂ : ∀ X : C', Triangle.mk (a'.app X) (adj₂.unit.app X) (w₂.app X) ∈ distTriang C')
    (ha : ∀ Y : C', R₁.map (a'.app Y) = a.app (R₁.obj Y))
    (hw : ∀ X : C, e.inv.app (E₁.obj X) ≫ Res₂.map (inv (α.app X)) ≫
      w₂.app (L₁.obj X) = L₁.map (w₁.app X) ≫ (L₁.commShiftIso (1 : ℤ)).hom.app X) :
    IsIso (mateEquiv adjL₁ adjL₂ (TwoSquare.mk _ _ _ _ (inv α))) := by
  have hU := isIso_mateEquiv_of_distTriang adjL₁ a a' adj₁.unit adj₂.unit w₁ w₂ hT₁ hT₂ ha
    ((TwoSquare.mk _ _ _ _ (inv α)).hComp (TwoSquare.mk _ _ _ _ e.inv)) (fun X ↦ by
      have hunit : L₁.map (adj₁.unit.app X) ≫ e.inv.app (E₁.obj X) =
          adj₂.unit.app (L₁.obj X) ≫ Res₂.map (α.app X) := by
        simpa [hα] using unit_mateEquiv adj₁ adj₂ α X
      simp [TwoSquare.hComp, reassoc_of% hunit])
    (fun X ↦ by simpa [TwoSquare.hComp] using hw X)
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

end Triangulated

end CategoryTheory
