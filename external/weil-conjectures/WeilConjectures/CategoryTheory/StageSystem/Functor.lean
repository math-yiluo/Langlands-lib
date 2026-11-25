/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic

/-!
# Descent of functors and natural transformations to pair categories

Let `S` and `S'` be stage systems on families of categories `C i` and `D i` indexed by the same
directed preorder. A *morphism of stage systems* `F : S.Morphism S'` is a family of functors
`Φ_i : C i ⥤ D i` together with isomorphisms `β_{j/i} : T'_{j/i} ∘ Φ_i ≅ Φ_j ∘ T_{j/i}` compatible
with the associators. It induces a functor `F.functor` between the pair categories, given on a
representative `u : T x ⟶ T y` at the stage `n` by `β ≫ Φ_n u ≫ β⁻¹`. Families of natural
transformations compatible with the `β` descend to natural transformations.

In the application, `Φ_E` is `Rf_{!,E}` or `Lg_E^*` on `D^b_c(-, E)` and `β` is the compatibility
with the extension of scalars `T_{F/E} = F ⊗ᴸ_E -`; the exchange maps at the finite stages
descend to the exchange map on `D^b_c(-, ℚ̄_ℓ)`.

## Main definitions

- `CategoryTheory.StageSystem.Morphism`: morphisms of stage systems.
- `CategoryTheory.StageSystem.Morphism.functor`: the induced functor on pair categories.
- `CategoryTheory.StageSystem.Morphism.Hom` and `CategoryTheory.StageSystem.Morphism.descNatTrans`:
  compatible families of natural transformations and the induced natural transformations.
- `CategoryTheory.StageSystem.Morphism.id`, `CategoryTheory.StageSystem.Morphism.comp`, with
  `functorIdIso` and `functorCompIso`.

## Main statements

- `CategoryTheory.StageSystem.Morphism.isIso_descNatTrans`: a descended natural transformation
  whose components at the finite stages are isomorphisms is an isomorphism.
-/

@[expose] public section

universe w v u v' u' v'' u''

namespace CategoryTheory

open Category

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)] {E : I → Type u''} [∀ i, Category.{v''} (E i)]

/-- A *morphism of stage systems* `S ⟶ S'`: functors `Φ_i : C i ⥤ D i` at every stage and
isomorphisms `β_{j/i} : Φ_i ⋙ T'_{j/i} ≅ T_{j/i} ⋙ Φ_j` compatible with the associators
(the families `(Φ_E, β_{F/E})`). -/
structure Morphism (S : StageSystem C) (S' : StageSystem D) where
  /-- The functors at the finite stages. -/
  Φ : ∀ i, C i ⥤ D i
  /-- The compatibility with the transition functors. -/
  β : ∀ {i j : I} (h : i ≤ j), Φ i ⋙ S'.T h ≅ S.T h ⋙ Φ j
  /-- The compatibility of `β` with the associators. -/
  coh : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (x : C i),
    (S'.T h').map ((β h).hom.app x) ≫ (β h').hom.app ((S.T h).obj x) ≫
      (Φ k).map ((S.assoc h h').hom.app x) =
    (S'.assoc h h').hom.app ((Φ i).obj x) ≫ (β (h.trans h')).hom.app x

namespace Morphism

variable {S : StageSystem C} {S' : StageSystem D} {S'' : StageSystem E} (F : Morphism S S')

/-- The value of a morphism of stage systems on a morphism at the stage `n`. -/
def mapAt {i j n : I} {hi : i ≤ n} {hj : j ≤ n} {x : C i} {y : C j}
    (u : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    (S'.T hi).obj ((F.Φ i).obj x) ⟶ (S'.T hj).obj ((F.Φ j).obj y) :=
  (F.β hi).hom.app x ≫ (F.Φ n).map u ≫ (F.β hj).inv.app y

lemma coh_inv {i j k : I} (h : i ≤ j) (h' : j ≤ k) (x : C i) :
    (F.Φ k).map ((S.assoc h h').inv.app x) ≫ (F.β h').inv.app ((S.T h).obj x) ≫
      (S'.T h').map ((F.β h).inv.app x) =
    (F.β (h.trans h')).inv.app x ≫ (S'.assoc h h').inv.app ((F.Φ i).obj x) := by
  rw [← cancel_epi ((S'.T h').map ((F.β h).hom.app x) ≫ (F.β h').hom.app ((S.T h).obj x) ≫
      (F.Φ k).map ((S.assoc h h').hom.app x))]
  conv_rhs => rw [F.coh]
  simp [← Functor.map_comp_assoc, ← Functor.map_comp]

@[simp]
lemma mapAt_id {i n : I} {hi : i ≤ n} (x : C i) :
    F.mapAt (hi := hi) (hj := hi) (𝟙 ((S.T hi).obj x)) = 𝟙 _ := by
  simp [mapAt]

@[simp]
lemma mapAt_comp {i j k n : I} {hi : i ≤ n} {hj : j ≤ n} {hk : k ≤ n} {x : C i} {y : C j}
    {z : C k} (u : (S.T hi).obj x ⟶ (S.T hj).obj y) (v : (S.T hj).obj y ⟶ (S.T hk).obj z) :
    F.mapAt (u ≫ v) = F.mapAt u ≫ F.mapAt v := by
  simp [mapAt]

/-- The value of a morphism of stage systems commutes with transport. -/
lemma tr_mapAt {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x : C i} {y : C j}
    (u : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    S'.tr h (F.mapAt u) = F.mapAt (S.tr h u) := by
  have nat := (F.β h).hom.naturality u
  simp only [Functor.comp_map] at nat
  have e₁ := F.coh hi h x
  have e₂ := F.coh_inv hj h y
  have E₁ : (S'.assoc hi h).inv.app ((F.Φ i).obj x) ≫ (S'.T h).map ((F.β hi).hom.app x) =
      (F.β (hi.trans h)).hom.app x ≫ (F.Φ p).map ((S.assoc hi h).inv.app x) ≫
        (F.β h).inv.app ((S.T hi).obj x) := by
    rw [← cancel_epi ((S'.assoc hi h).hom.app ((F.Φ i).obj x)), Iso.hom_inv_id_app_assoc,
      ← reassoc_of% e₁]
    simp [← Functor.map_comp_assoc]
  have E₂ : (S'.T h).map ((F.β hj).inv.app y) ≫ (S'.assoc hj h).hom.app ((F.Φ j).obj y) =
      (F.β h).hom.app ((S.T hj).obj y) ≫ (F.Φ p).map ((S.assoc hj h).hom.app y) ≫
        (F.β (hj.trans h)).inv.app y := by
    rw [← cancel_mono ((S'.assoc hj h).inv.app ((F.Φ j).obj y))]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    rw [← e₂]
    simp [← Functor.map_comp_assoc]
  simp only [tr, mapAt, Functor.map_comp, Category.assoc]
  rw [reassoc_of% E₁, E₂, reassoc_of% nat, Iso.inv_hom_id_app_assoc]

variable [IsDirectedOrder I]

open PairCategory

/-- The functor on pair categories induced by a morphism of stage systems: `(i, x) ↦ (i, Φ_i x)`,
and a representative `u : T x ⟶ T y` at the stage `n` goes to `β ≫ Φ_n u ≫ β⁻¹`. -/
noncomputable def functor : S.PairCategory ⥤ S'.PairCategory where
  obj X := ⟨X.stage, (F.Φ X.stage).obj X.obj⟩
  map {X Y} f := Quotient.map (sa := Rep.setoid X Y) (sb := Rep.setoid _ _)
    (fun r ↦ ⟨r.k, r.hX, r.hY, F.mapAt r.u⟩)
    (fun r s ⟨p, hr, hs, e⟩ ↦ ⟨p, hr, hs, by
      change S'.tr hr (F.mapAt r.u) = S'.tr hs (F.mapAt s.u)
      rw [F.tr_mapAt, F.tr_mapAt, e]⟩) f
  map_id X := by
    rw [id_eq_mkHom X le_rfl, id_eq_mkHom _ le_rfl]
    exact congr_arg (mkHom _ _ _) (F.mapAt_id _)
  map_comp {X Y Z} f g := by
    obtain ⟨n, -, hX, hY, hY', hZ, u, v, rfl, rfl⟩ := exists_common_stage f g X.stage
    rw [mkHom_comp_mkHom]
    change mkHom _ _ _ _ = mkHom _ _ _ _ ≫ mkHom _ _ _ _
    rw [mkHom_comp_mkHom, F.mapAt_comp]

lemma functor_obj (X : S.PairCategory) :
    F.functor.obj X = ⟨X.stage, (F.Φ X.stage).obj X.obj⟩ := rfl

lemma functor_map_mkHom {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
    (u : X.toStage hX ⟶ Y.toStage hY) :
    F.functor.map (mkHom n hX hY u) =
      mkHom (X := F.functor.obj X) (Y := F.functor.obj Y) n hX hY (F.mapAt u) := rfl

omit [IsDirectedOrder I] in
lemma mapAt_map {i n : I} {hi : i ≤ n} {x y : C i} (f : x ⟶ y) :
    F.mapAt (hi := hi) (hj := hi) ((S.T hi).map f) = (S'.T hi).map ((F.Φ i).map f) := by
  have := (F.β hi).hom.naturality f
  simp only [Functor.comp_map] at this
  simp [mapAt, ← reassoc_of% this]

lemma functor_map_ι {i : I} {x y : C i} (f : x ⟶ y) :
    F.functor.map ((S.ι i).map f) = (S'.ι i).map ((F.Φ i).map f) := by
  change F.functor.map (mkHom _ _ _ _) = mkHom _ _ _ _
  rw [functor_map_mkHom, mapAt_map]
  rfl

/-- The functor on pair categories induced by a morphism of stage systems is compatible with the
stage inclusions: `Φ ∘ j_i = j_i ∘ Φ_i`. -/
noncomputable def ιCompFunctorIso (i : I) : S.ι i ⋙ F.functor ≅ F.Φ i ⋙ S'.ι i :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    simp only [Functor.comp_map, Iso.refl_hom, comp_id, id_comp]
    exact F.functor_map_ι f)

@[simp]
lemma ιCompFunctorIso_hom_app (i : I) (x : C i) :
    (F.ιCompFunctorIso i).hom.app x = 𝟙 _ := rfl

@[simp]
lemma ιCompFunctorIso_inv_app (i : I) (x : C i) :
    (F.ιCompFunctorIso i).inv.app x = 𝟙 _ := rfl

/-- A compatible family of natural transformations between two morphisms of stage systems. -/
@[ext]
structure Hom (F G : Morphism S S') where
  /-- The natural transformations at the finite stages. -/
  τ : ∀ i, F.Φ i ⟶ G.Φ i
  /-- The compatibility with the `β`. -/
  comm : ∀ {i j : I} (h : i ≤ j) (x : C i),
    (S'.T h).map ((τ i).app x) ≫ (G.β h).hom.app x = (F.β h).hom.app x ≫ (τ j).app ((S.T h).obj x)

attribute [reassoc] Hom.comm

variable {F} {G H : Morphism S S'}

omit [IsDirectedOrder I] in
lemma Hom.comm_inv (τ : Hom F G) {i j : I} (h : i ≤ j) (x : C i) :
    (F.β h).inv.app x ≫ (S'.T h).map ((τ.τ i).app x) =
      (τ.τ j).app ((S.T h).obj x) ≫ (G.β h).inv.app x := by
  rw [← cancel_epi ((F.β h).hom.app x), Iso.hom_inv_id_app_assoc, ← τ.comm_assoc,
    Iso.hom_inv_id_app]
  erw [Category.comp_id]

omit [IsDirectedOrder I] in
lemma Hom.mapAt_naturality (τ : Hom F G) {i j n : I} {hi : i ≤ n} {hj : j ≤ n} {x : C i}
    {y : C j} (u : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    F.mapAt u ≫ (S'.T hj).map ((τ.τ j).app y) = (S'.T hi).map ((τ.τ i).app x) ≫ G.mapAt u := by
  simp only [mapAt, Category.assoc]
  rw [τ.comm_inv, (τ.τ n).naturality_assoc, τ.comm_assoc]

/-- The natural transformation of descended functors induced by a compatible family of natural
transformations: its component at `(i, x)` is `j_i(τ_i x)`. -/
noncomputable def descNatTrans (τ : Hom F G) : F.functor ⟶ G.functor where
  app X := (S'.ι X.stage).map ((τ.τ X.stage).app X.obj)
  naturality {X Y} f := by
    induction f using hom_induction with
    | h n hX hY u =>
      rw [functor_map_mkHom, functor_map_mkHom, ι_map_eq hX, ι_map_eq hY]
      change mkHom _ _ _ _ ≫ mkHom _ _ _ _ = mkHom _ _ _ _ ≫ mkHom _ _ _ _
      rw [mkHom_comp_mkHom, mkHom_comp_mkHom]
      exact congr_arg (mkHom _ _ _) (τ.mapAt_naturality u)

lemma descNatTrans_app (τ : Hom F G) (X : S.PairCategory) :
    (descNatTrans τ).app X = (S'.ι X.stage).map ((τ.τ X.stage).app X.obj) := rfl

/-- The identity family. -/
@[simps]
def Hom.id (F : Morphism S S') : Hom F F where
  τ _ := 𝟙 _
  comm _ _ := by simp

/-- Composition of families. -/
@[simps]
def Hom.comp (τ : Hom F G) (τ' : Hom G H) : Hom F H where
  τ i := τ.τ i ≫ τ'.τ i
  comm h x := by simp [τ'.comm, τ.comm_assoc]

@[simp]
lemma descNatTrans_id (F : Morphism S S') : descNatTrans (Hom.id F) = 𝟙 _ := by
  ext X
  simp [descNatTrans_app]
  rfl

@[simp]
lemma descNatTrans_comp (τ : Hom F G) (τ' : Hom G H) :
    descNatTrans (τ.comp τ') = descNatTrans τ ≫ descNatTrans τ' := by
  ext X
  simp [descNatTrans_app]

/-- An isomorphism of descended functors induced by a compatible family of isomorphisms. -/
@[simps]
noncomputable def descNatIso (τ : Hom F G) (τ' : Hom G F) (h₁ : τ.comp τ' = Hom.id F)
    (h₂ : τ'.comp τ = Hom.id G) : F.functor ≅ G.functor where
  hom := descNatTrans τ
  inv := descNatTrans τ'
  hom_inv_id := by rw [← descNatTrans_comp, h₁, descNatTrans_id]
  inv_hom_id := by rw [← descNatTrans_comp, h₂, descNatTrans_id]

/-- A descended natural transformation whose components at the finite stages are isomorphisms is
an isomorphism (for instance, the descended exchange transformation is an isomorphism as soon
as it is one at every finite stage). -/
lemma isIso_descNatTrans (τ : Hom F G) (hτ : ∀ i, IsIso (τ.τ i)) : IsIso (descNatTrans τ) := by
  have : ∀ X : S.PairCategory, IsIso ((descNatTrans τ).app X) := fun X ↦ by
    rw [descNatTrans_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- A component of a descended natural transformation is an isomorphism as soon as the
component at its finite stage is. -/
lemma isIso_descNatTrans_app (τ : Hom F G) (X : S.PairCategory)
    (hτ : IsIso ((τ.τ X.stage).app X.obj)) : IsIso ((descNatTrans τ).app X) := by
  rw [descNatTrans_app]
  infer_instance

end Morphism

/-! ### Identity and composition -/

namespace Morphism

variable (S : StageSystem C)

/-- The identity morphism of a stage system. -/
@[simps]
def id : Morphism S S where
  Φ i := 𝟭 _
  β h := Iso.refl _
  coh h h' x := by simp

variable {S} {S' : StageSystem D} {S'' : StageSystem E}

/-- The composite of two morphisms of stage systems. -/
@[simps]
def comp (F : Morphism S S') (G : Morphism S' S'') : Morphism S S'' where
  Φ i := F.Φ i ⋙ G.Φ i
  β h := Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (F.Φ _) (G.β h) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (F.β h) (G.Φ _) ≪≫
      Functor.associator _ _ _
  coh {i j k} h h' x := by
    have e₁ := G.coh h h' ((F.Φ i).obj x)
    have e₂ := F.coh h h' x
    have n₁ := (G.β h').hom.naturality ((F.β h).hom.app x)
    simp only [Functor.comp_map] at n₁
    dsimp
    simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
    conv_rhs => rw [← reassoc_of% e₁, ← Functor.map_comp, ← e₂]
    simp only [Functor.map_comp]
    rw [reassoc_of% n₁]

@[simp]
lemma id_β_hom_app {i j : I} (h : i ≤ j) (x : C i) :
    ((id S).β h).hom.app x = 𝟙 ((S.T h).obj x) := rfl

@[simp]
lemma id_β_inv_app {i j : I} (h : i ≤ j) (x : C i) :
    ((id S).β h).inv.app x = 𝟙 ((S.T h).obj x) := rfl

@[simp]
lemma comp_β_hom_app (F : Morphism S S') (G : Morphism S' S'') {i j : I} (h : i ≤ j) (x : C i) :
    ((F.comp G).β h).hom.app x =
      (G.β h).hom.app ((F.Φ i).obj x) ≫ (G.Φ j).map ((F.β h).hom.app x) := by
  simp only [comp_β, Iso.trans_hom, NatTrans.comp_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

@[simp]
lemma comp_β_inv_app (F : Morphism S S') (G : Morphism S' S'') {i j : I} (h : i ≤ j) (x : C i) :
    ((F.comp G).β h).inv.app x =
      (G.Φ j).map ((F.β h).inv.app x) ≫ (G.β h).inv.app ((F.Φ i).obj x) := by
  rw [← cancel_epi (((F.comp G).β h).hom.app x), Iso.hom_inv_id_app, comp_β_hom_app,
    Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  rfl

variable [IsDirectedOrder I]

open PairCategory

/-- The functor induced by the identity morphism is the identity. -/
noncomputable def functorIdIso : (id S).functor ≅ 𝟭 S.PairCategory :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {X Y} f ↦ by
    induction f using hom_induction with
    | h n hX hY u =>
      simp only [Iso.refl_hom, comp_id, id_comp, Functor.id_map]
      rw [functor_map_mkHom]
      congr 1
      simp only [mapAt, id_β, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
      erw [Category.id_comp, Category.comp_id]
      rfl)

@[simp]
lemma functorIdIso_hom_app (X : S.PairCategory) : (functorIdIso (S := S)).hom.app X = 𝟙 _ := rfl

@[simp]
lemma functorIdIso_inv_app (X : S.PairCategory) : (functorIdIso (S := S)).inv.app X = 𝟙 _ := rfl

/-- The functor induced by a composite is the composite of the induced functors. -/
noncomputable def functorCompIso (F : Morphism S S') (G : Morphism S' S'') :
    (F.comp G).functor ≅ F.functor ⋙ G.functor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {X Y} f ↦ by
    induction f using hom_induction with
    | h n hX hY u =>
      simp only [Iso.refl_hom, comp_id, id_comp, Functor.comp_map]
      rw [functor_map_mkHom, functor_map_mkHom, functor_map_mkHom]
      congr 1
      simp only [mapAt, Functor.comp_obj, comp_β, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
        Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.associator_hom_app,
        Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app, comp_id,
        id_comp, Iso.trans_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv, Category.assoc,
        Functor.isoWhiskerLeft_inv, Functor.map_comp]
      erw [Category.id_comp, Category.id_comp]
      rfl)

@[simp]
lemma functorCompIso_hom_app (F : Morphism S S') (G : Morphism S' S'') (X : S.PairCategory) :
    (functorCompIso F G).hom.app X = 𝟙 _ := rfl

@[simp]
lemma functorCompIso_inv_app (F : Morphism S S') (G : Morphism S' S'') (X : S.PairCategory) :
    (functorCompIso F G).inv.app X = 𝟙 _ := rfl

/-- The functor induced by the identity morphism acts as the identity on morphisms. -/
@[simp]
lemma functor_id_map {X Y : S.PairCategory} (f : X ⟶ Y) : (id S).functor.map f = f := by
  simpa using (functorIdIso (S := S)).hom.naturality f

/-- The functor induced by a composite acts on morphisms as the composite of the induced
functors. -/
@[simp]
lemma functor_comp_map (F : Morphism S S') (G : Morphism S' S'') {X Y : S.PairCategory}
    (f : X ⟶ Y) : (F.comp G).functor.map f = G.functor.map (F.functor.map f) := by
  simpa using (functorCompIso F G).hom.naturality f

end Morphism

end StageSystem

end CategoryTheory
