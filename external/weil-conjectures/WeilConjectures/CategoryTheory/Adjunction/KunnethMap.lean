/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory

/-!

# Künneth maps of adjunctions with oplax monoidal left adjoints

Let `F ⊣ G` be an adjunction between monoidal categories whose left adjoint `F` is oplax
monoidal. Besides the projection morphism `G A ⊗ B ⟶ G (A ⊗ F B)`
(`CategoryTheory.Adjunction.projectionMorphism`), there is a *left projection morphism*
`B ⊗ G A ⟶ G (F B ⊗ A)` (`CategoryTheory.Adjunction.leftProjectionMorphism`), the transpose of
`F (B ⊗ G A) ⟶ F B ⊗ F G A ⟶ F B ⊗ A`. If `F` is compatible with braidings, the two
morphisms agree up to the braidings (`CategoryTheory.Adjunction.leftProjectionMorphism_eq`).

The transpose of `F (X ⊗ E) ⟶ F X ⊗ F E ⟶ A ⊗ F E` along `F ⊣ G`, for a morphism
`c : F X ⟶ A`, is the transpose of `c` followed by the projection morphism
(`CategoryTheory.Adjunction.homEquiv_δ_whiskerRight`), and similarly on the left. Applied to a
composite `Q ≅ S ⋙ R` of adjunctions this shows that the *Künneth map*
```
U ⊗ V ⟶ Q_* (A₁ ⊗ A₂),
```
the transpose of `Q (U ⊗ V) ⟶ Q U ⊗ Q V ⟶ A₁ ⊗ A₂` for morphisms `Q U ⟶ A₁` and `Q V ⟶ A₂`,
is a composite of a transpose along `S`, a left projection morphism of `S`, a transpose along
`R` and a projection morphism of `R` (`CategoryTheory.Adjunction.homEquiv_δ_tensorHom_eq`). In
the application to the six functors these are the base change morphisms and the projection
formulas for the two factors of a product morphism `f₁ × f₂ = (f₁ × 1) ≫ (1 × f₂)`.

## Main definitions

- `CategoryTheory.Adjunction.leftProjectionMorphism`: `B ⊗ G A ⟶ G (F B ⊗ A)`.

## Main statements

- `CategoryTheory.Adjunction.isIso_leftProjectionMorphism`: the left projection morphism is an
  isomorphism if the projection morphism is, for `F` compatible with braidings.
- `CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom`: the Künneth map of a composite is an
  isomorphism if the base change morphisms and projection morphisms of the factors are.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

section ProjectionMorphisms

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]
/-- The projection morphism `G A ⊗ B ⟶ G (A ⊗ F B)` of an adjunction `F ⊣ G` with `F` oplax
monoidal: the adjoint of `F (G A ⊗ B) ⟶ F G A ⊗ F B ⟶ A ⊗ F B`. -/
noncomputable def projectionMorphism (A : C) (B : D) : G.obj A ⊗ B ⟶ G.obj (A ⊗ F.obj B) :=
  adj.homEquiv _ _ (δ F (G.obj A) B ≫ adj.counit.app A ▷ F.obj B)

/-- The projection morphism is natural in its second variable. -/
@[reassoc]
lemma projectionMorphism_natural_right (A : C) {B B' : D} (h : B ⟶ B') :
    G.obj A ◁ h ≫ adj.projectionMorphism A B' =
      adj.projectionMorphism A B ≫ G.map (A ◁ F.map h) := by
  rw [projectionMorphism, projectionMorphism, ← homEquiv_naturality_left,
    ← homEquiv_naturality_right]
  congr 1
  rw [← δ_natural_right_assoc, whisker_exchange, Category.assoc]
  rfl

/-- The projection morphism is natural in its first variable. -/
@[reassoc]
lemma projectionMorphism_natural_left {A A' : C} (φ : A ⟶ A') (B : D) :
    G.map φ ▷ B ≫ adj.projectionMorphism A' B =
      adj.projectionMorphism A B ≫ G.map (φ ▷ F.obj B) := by
  rw [projectionMorphism, projectionMorphism, ← homEquiv_naturality_left,
    ← homEquiv_naturality_right, ← δ_natural_left_assoc, Category.assoc, ← comp_whiskerRight,
    ← comp_whiskerRight]
  congr 3
  exact adj.counit.naturality φ


/-- The *left projection morphism* `B ⊗ G A ⟶ G (F B ⊗ A)` of an adjunction `F ⊣ G` with `F`
oplax monoidal: the adjoint of `F (B ⊗ G A) ⟶ F B ⊗ F G A ⟶ F B ⊗ A`. -/
noncomputable def leftProjectionMorphism (B : D) (A : C) : B ⊗ G.obj A ⟶ G.obj (F.obj B ⊗ A) :=
  adj.homEquiv _ _ (δ F B (G.obj A) ≫ F.obj B ◁ adj.counit.app A)

omit [MonoidalCategory C] [MonoidalCategory D] [F.OplaxMonoidal] in
lemma map_homEquiv_comp_counit {X : D} {A : C} (c : F.obj X ⟶ A) :
    F.map (adj.homEquiv _ _ c) ≫ adj.counit.app A = c := by
  simp [homEquiv_unit]

/-- The transpose of `F (X ⊗ E) ⟶ F X ⊗ F E ⟶ A ⊗ F E` is the transpose of `F X ⟶ A` followed
by the projection morphism: writing `c♯ : X ⟶ G A` for the transpose of `c`, the transpose of
the top row is the composite of the bottom row in
```
F (X ⊗ E) ──δ──▶ F X ⊗ F E ──c ▷ F E──▶ A ⊗ F E
X ⊗ E ──c♯ ▷ E──▶ G A ⊗ E ──projectionMorphism──▶ G (A ⊗ F E)
```
-/
lemma homEquiv_δ_whiskerRight {X : D} {A : C} (c : F.obj X ⟶ A) (E : D) :
    adj.homEquiv _ _ (δ F X E ≫ c ▷ F.obj E) =
      adj.homEquiv _ _ c ▷ E ≫ adj.projectionMorphism A E := by
  rw [projectionMorphism, ← homEquiv_naturality_left, ← δ_natural_left_assoc,
    ← comp_whiskerRight, map_homEquiv_comp_counit]

/-- The transpose of `F (E ⊗ X) ⟶ F E ⊗ F X ⟶ F E ⊗ A` is the transpose of `F X ⟶ A` followed
by the left projection morphism: writing `c♯ : X ⟶ G A` for the transpose of `c`, the
transpose of the top row is the composite of the bottom row in
```
F (E ⊗ X) ──δ──▶ F E ⊗ F X ──F E ◁ c──▶ F E ⊗ A
E ⊗ X ──E ◁ c♯──▶ E ⊗ G A ──leftProjectionMorphism──▶ G (F E ⊗ A)
```
-/
lemma homEquiv_δ_whiskerLeft {X : D} {A : C} (c : F.obj X ⟶ A) (E : D) :
    adj.homEquiv _ _ (δ F E X ≫ F.obj E ◁ c) =
      E ◁ adj.homEquiv _ _ c ≫ adj.leftProjectionMorphism E A := by
  rw [leftProjectionMorphism, ← homEquiv_naturality_left, ← δ_natural_right_assoc,
    ← whiskerLeft_comp, map_homEquiv_comp_counit]

variable [BraidedCategory C] [BraidedCategory D]

/-- For `F` compatible with the braidings, the left projection morphism is the projection
morphism conjugated by the braidings: the square
```
B ⊗ G A ───────leftProjectionMorphism───────▶ G (F B ⊗ A)
   │ β                                             ▲ G β⁻¹
   ▼                                               │
G A ⊗ B ─────────projectionMorphism──────────▶ G (A ⊗ F B)
```
commutes. -/
lemma leftProjectionMorphism_eq
    (h : ∀ X Y : D, δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom = F.map (β_ X Y).hom ≫ δ F Y X)
    (B : D) (A : C) :
    adj.leftProjectionMorphism B A =
      (β_ B (G.obj A)).hom ≫ adj.projectionMorphism A B ≫ G.map (β_ (F.obj B) A).inv := by
  rw [leftProjectionMorphism, projectionMorphism, ← homEquiv_naturality_right,
    ← homEquiv_naturality_left]
  congr 1
  simp only [Category.assoc]
  erw [BraidedCategory.braiding_inv_naturality_left]
  rw [reassoc_of% (h B (G.obj A)).symm]
  exact (congrArg _ (Iso.hom_inv_id_assoc _ _)).symm

/-- For `F` compatible with the braidings, the left projection morphism is an isomorphism if the
projection morphism is. -/
lemma isIso_leftProjectionMorphism
    (h : ∀ X Y : D, δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom = F.map (β_ X Y).hom ≫ δ F Y X)
    (B : D) (A : C) [IsIso (adj.projectionMorphism A B)] :
    IsIso (adj.leftProjectionMorphism B A) := by
  rw [adj.leftProjectionMorphism_eq h]
  infer_instance

end ProjectionMorphisms

section Restrict

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  {F : D ⥤ C} [F.Monoidal] {G : C ⥤ D} (adj : F ⊣ G)
  (hF : ∀ X : Q.FullSubcategory, P (F.obj X.obj)) (hG : ∀ X : P.FullSubcategory, Q (G.obj X.obj))

/-- The projection morphism of the restriction of an adjunction `F ⊣ G` to full monoidal
subcategories is the projection morphism of `F ⊣ G`. -/
lemma ι_map_projectionMorphism_restrictFullyFaithful (A : P.FullSubcategory)
    (B : Q.FullSubcategory) :
    Q.ι.map ((adj.restrictFullyFaithful Q.fullyFaithfulι P.fullyFaithfulι
      (P.liftCompιIso (Q.ι ⋙ F) hF).symm (Q.liftCompιIso (P.ι ⋙ G) hG).symm).projectionMorphism
        A B) = adj.projectionMorphism A.obj B.obj := by
  rw [projectionMorphism, projectionMorphism, restrictFullyFaithful_homEquiv_apply,
    Functor.FullyFaithful.map_preimage, homEquiv_unit]
  congr 1
  simp only [ObjectProperty.liftCompιIso, Iso.symm_hom, Iso.refl_inv, Functor.map_comp]
  erw [Functor.map_id, Category.id_comp, Category.comp_id]
  congr 1
  refine congrArg G.map (congrArg (· ▷ F.obj B.obj) ?_)
  exact (adj.map_restrictFullyFaithful_counit_app Q.fullyFaithfulι P.fullyFaithfulι _ _ A).trans
    (by simp)

end Restrict

section Composite

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]
  {R' : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} (adjR : R' ⊣ R)
  {S' : C₃ ⥤ C₂} {S : C₂ ⥤ C₃} (adjS : S' ⊣ S)
  {Q' : C₃ ⥤ C₁} {Q : C₁ ⥤ C₃} (adjQ : Q' ⊣ Q)

/-- Transposing along an adjunction `Q' ⊣ Q` with `Q' ≅ S' ⋙ R'` is transposing along `R' ⊣ R`
and then along `S' ⊣ S`, followed by the identification `R ⋙ S ≅ Q` of right adjoints: for
`g : Q' U ⟶ A`, with `h = e⁻¹ ≫ g : R' (S' U) ⟶ A`, `h♭ : S' U ⟶ R A` its transpose along
`R' ⊣ R` and `h♭♭ : U ⟶ S (R A)` the transpose of `h♭` along `S' ⊣ S`, the triangle
```
U ───────h♭♭──────▶ S (R A)
  ╲                    │ ≅
   g♯ ╲                ▼
        ╲──────────▶ Q A
```
commutes, where `g♯` is the transpose of `g` along `Q' ⊣ Q`. -/
lemma homEquiv_eq_homEquiv_homEquiv (e : Q' ≅ S' ⋙ R') {U : C₃} {A : C₁} (g : Q'.obj U ⟶ A) :
    adjQ.homEquiv _ _ g =
      adjS.homEquiv _ _ (adjR.homEquiv _ _ (e.inv.app U ≫ g)) ≫
        (rightAdjointUniq ((adjS.comp adjR).ofNatIsoLeft e.symm) adjQ).hom.app A := by
  apply (adjQ.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, homEquiv_counit, Functor.map_comp, Category.assoc,
    rightAdjointUniq_hom_app_counit,
    ← homEquiv_counit (adj := (adjS.comp adjR).ofNatIsoLeft e.symm),
    homEquiv_ofNatIsoLeft_symm_apply, comp_homEquiv]
  simp

variable [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃] [R'.OplaxMonoidal]
  [S'.OplaxMonoidal] [Q'.OplaxMonoidal]

/-- **The Künneth map of a composite.** Let `Q' ≅ S' ⋙ R'` be compatible with the oplax monoidal
structures, let `c₁ : Q' U ⟶ A₁` and `c₂ : Q' V ⟶ A₂`, and suppose that `c₂` comes from
`d₂ : S' V ⟶ W` up to an isomorphism `i₂ : R' W ≅ A₂`. Then the transpose of
`Q' (U ⊗ V) ⟶ Q' U ⊗ Q' V ⟶ A₁ ⊗ A₂` is the composite
```
U ⊗ V ⟶ U ⊗ S W ⟶ S (S' U ⊗ W) ⟶ S (R A₁ ⊗ W) ⟶ S R (A₁ ⊗ R' W) ⟶ S R (A₁ ⊗ A₂) ≅ Q (A₁ ⊗ A₂)
```
of the transpose of `d₂`, the left projection morphism of `S`, the transpose `h₁` of
`Q' U ≅ R' S' U ⟶ A₁`, the projection morphism of `R` and `i₂`. -/
lemma homEquiv_δ_tensorHom_eq (e : Q' ≅ S' ⋙ R')
    (he : ∀ U V : C₃, δ Q' U V ≫ (e.hom.app U ⊗ₘ e.hom.app V) =
      e.hom.app (U ⊗ V) ≫ R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V))
    {U V : C₃} {A₁ A₂ : C₁} (c₁ : Q'.obj U ⟶ A₁) (c₂ : Q'.obj V ⟶ A₂) {W : C₂}
    (d₂ : S'.obj V ⟶ W) (i₂ : R'.obj W ⟶ A₂) (hc₂ : e.inv.app V ≫ c₂ = R'.map d₂ ≫ i₂) :
    adjQ.homEquiv _ _ (δ Q' U V ≫ (c₁ ⊗ₘ c₂)) =
      U ◁ adjS.homEquiv _ _ d₂ ≫ adjS.leftProjectionMorphism U W ≫
        S.map (adjR.homEquiv _ _ (e.inv.app U ≫ c₁) ▷ W ≫ adjR.projectionMorphism A₁ W ≫
          R.map (A₁ ◁ i₂)) ≫
        (rightAdjointUniq ((adjS.comp adjR).ofNatIsoLeft e.symm) adjQ).hom.app _ := by
  have hδ : e.inv.app (U ⊗ V) ≫ δ Q' U V =
      R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V) ≫ (e.inv.app U ⊗ₘ e.inv.app V) := by
    rw [← cancel_epi (e.hom.app (U ⊗ V)), Iso.hom_inv_id_app_assoc, ← reassoc_of% he U V,
      tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app, id_tensorHom_id,
      Category.comp_id]
  have key : e.inv.app (U ⊗ V) ≫ δ Q' U V ≫ (c₁ ⊗ₘ c₂) =
      R'.map (δ S' U V ≫ S'.obj U ◁ d₂) ≫
        (δ R' (S'.obj U) W ≫ (e.inv.app U ≫ c₁) ▷ R'.obj W) ≫ A₁ ◁ i₂ := by
    rw [reassoc_of% hδ, tensorHom_comp_tensorHom, hc₂, Functor.map_comp, Category.assoc,
      Category.assoc, ← δ_natural_right_assoc, whisker_exchange_assoc, tensorHom_def,
      MonoidalCategory.whiskerLeft_comp]
  rw [homEquiv_eq_homEquiv_homEquiv adjR adjS adjQ e, key, homEquiv_naturality_left (adj := adjR),
    homEquiv_naturality_right (adj := adjR), homEquiv_δ_whiskerRight,
    homEquiv_naturality_right (adj := adjS), homEquiv_δ_whiskerLeft]
  simp only [Category.assoc, Functor.map_comp]

/-- **The Künneth map of a composite is an isomorphism** if the transposes of `d₂` and of
`Q' U ≅ R' S' U ⟶ A₁`, the left projection morphism of `S` at `(U, W)`, the projection morphism
of `R` at `(A₁, W)` and `i₂` are isomorphisms (`homEquiv_δ_tensorHom_eq`). -/
lemma isIso_homEquiv_δ_tensorHom (e : Q' ≅ S' ⋙ R')
    (he : ∀ U V : C₃, δ Q' U V ≫ (e.hom.app U ⊗ₘ e.hom.app V) =
      e.hom.app (U ⊗ V) ≫ R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V))
    {U V : C₃} {A₁ A₂ : C₁} (c₁ : Q'.obj U ⟶ A₁) (c₂ : Q'.obj V ⟶ A₂) {W : C₂}
    (d₂ : S'.obj V ⟶ W) (i₂ : R'.obj W ⟶ A₂) (hc₂ : e.inv.app V ≫ c₂ = R'.map d₂ ≫ i₂)
    [IsIso (adjS.homEquiv _ _ d₂)] [IsIso (adjS.leftProjectionMorphism U W)]
    [IsIso (adjR.homEquiv _ _ (e.inv.app U ≫ c₁))] [IsIso (adjR.projectionMorphism A₁ W)]
    [IsIso i₂] :
    IsIso (adjQ.homEquiv _ _ (δ Q' U V ≫ (c₁ ⊗ₘ c₂))) := by
  rw [homEquiv_δ_tensorHom_eq adjR adjS adjQ e he c₁ c₂ d₂ i₂ hc₂]
  infer_instance

end Composite

end CategoryTheory.Adjunction
