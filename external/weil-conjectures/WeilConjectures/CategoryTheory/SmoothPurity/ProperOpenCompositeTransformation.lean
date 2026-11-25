/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # The functorial word underlying ordinary proper/open alpha

Source: the intrinsic composition of Stacks Project, Tag 0F7B, written in functor categories.
(blueprint: lem-cbc-proper-open-word-components)
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory.Functor

/-- Package the specified beta, projector and comparison maps before specialization.
Source: Stacks Project, Tag 0F7B, intrinsic ordinary construction.
(blueprint: lem-cbc-proper-open-word-components). -/
@[irreducible] def properOpenCompositeTransformation
    (A C D E T : Type*) [Category A] [Category C] [Category D]
    [Category E] [Category T]
    (I : A ⥤ T) (P : T ⥤ C) (Q : A ⥤ D) (L : D ⥤ E)
    (J : E ⥤ D) (H : D ⥤ C) (K : E ⥤ C) (R : A ⥤ E)
    (b : I ⋙ P ⟶ Q ⋙ H) (d : 𝟭 D ⟶ L ⋙ J)
    (t : J ⋙ H ⟶ K) (c : Q ⋙ L ⟶ R) : I ⋙ P ⟶ R ⋙ K :=
  b ≫ whiskerRight (whiskerLeft Q d) H ≫
    whiskerRight (associator Q L J).inv H ≫
    (associator (Q ⋙ L) J H).hom ≫
    whiskerLeft (Q ⋙ L) t ≫ whiskerRight c K

/-- Evaluate the comparison word at an object.
Source: component formulas for whiskering and functor associators in Mathlib.
(blueprint: lem-cbc-proper-open-word-components).
Proof: evaluate each natural transformation in the defining composite. Both
associator components are identities, and functors preserve identities. Remove
these identities and reassociate the four remaining morphisms. -/
theorem properOpenCompositeTransformation_app
    (A C D E T : Type*) [Category A] [Category C] [Category D]
    [Category E] [Category T]
    (I : A ⥤ T) (P : T ⥤ C) (Q : A ⥤ D) (L : D ⥤ E)
    (J : E ⥤ D) (H : D ⥤ C) (K : E ⥤ C) (R : A ⥤ E)
    (b : I ⋙ P ⟶ Q ⋙ H) (d : 𝟭 D ⟶ L ⋙ J)
    (t : J ⋙ H ⟶ K) (c : Q ⋙ L ⟶ R) (M : A) :
    (properOpenCompositeTransformation A C D E T I P Q L J H K R b d t c).app M =
      b.app M ≫ H.map (d.app (Q.obj M)) ≫
        t.app (L.obj (Q.obj M)) ≫ K.map (c.app M) := by
  simp only [properOpenCompositeTransformation, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, associator_hom_app, associator_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, comp_obj]

end CategoryTheory.Functor

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

private theorem unit_composite_restriction
    {D E F : Type*} [Category D] [Category E] [Category F]
    (L : D ⥤ E) (U : E ⥤ D) (H : D ⥤ F) (V : F ⥤ D)
    (K : E ⥤ F) (P : F ⥤ E)
    (g : P ≅ V ⋙ L) (j : U ⋙ H ≅ K)
    (us : 𝟭 E ≅ U ⋙ L) (ub : 𝟭 D ≅ H ⋙ V) (uk : 𝟭 E ≅ K ⋙ P)
    (hj : ∀ N, uk.hom.app N ≫ g.hom.app (K.obj N) =
      us.hom.app N ≫ L.map (ub.hom.app (U.obj N)) ≫ L.map (V.map (j.hom.app N)))
    (N : E) :
    P.map (j.hom.app N) ≫ uk.inv.app N =
      g.hom.app (H.obj (U.obj N)) ≫ L.map (ub.inv.app (U.obj N)) ≫ us.inv.app N := by
  apply (cancel_mono (uk.hom.app N ≫ g.hom.app (K.obj N))).1
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [hj]
  simp only [Iso.inv_hom_id_app_assoc, ← L.map_comp_assoc, Iso.inv_hom_id_app,
    ]
  simpa only [Functor.comp_obj, Functor.comp_map, CategoryTheory.Functor.map_id,
    Category.id_comp] using g.hom.naturality (j.hom.app N)

private theorem projector_restriction_word
    {A D E F : Type*} [Category A] [Category D] [Category E] [Category F]
    (Z : A ⥤ F) (Q : A ⥤ D) (L : D ⥤ E) (U : E ⥤ D)
    (H : D ⥤ F) (V : F ⥤ D) (K : E ⥤ F) (R : A ⥤ E) (P : F ⥤ E)
    (b : Z ≅ Q ⋙ H) (d : 𝟭 D ⟶ L ⋙ U)
    (g : P ≅ V ⋙ L) (j : U ⋙ H ≅ K) (c : R ≅ Q ⋙ L)
    (us : 𝟭 E ≅ U ⋙ L) (ub : 𝟭 D ≅ H ⋙ V) (uk : 𝟭 E ≅ K ⋙ P)
    (hd : ∀ M, L.map (d.app M) = us.hom.app (L.obj M))
    (hj : ∀ N, P.map (j.hom.app N) ≫ uk.inv.app N =
      g.hom.app (H.obj (U.obj N)) ≫ L.map (ub.inv.app (U.obj N)) ≫ us.inv.app N)
    (M : A) :
    P.map (b.hom.app M ≫ H.map (d.app (Q.obj M)) ≫
      j.hom.app (L.obj (Q.obj M)) ≫ K.map (c.inv.app M)) ≫ uk.inv.app (R.obj M) =
      g.hom.app (Z.obj M) ≫ L.map (V.map (b.hom.app M) ≫ ub.inv.app (Q.obj M)) ≫
        c.inv.app M := by
  have hu := uk.inv.naturality (c.inv.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  simp only [P.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj] at hu
  rw [hu]
  rw [reassoc_of% hj]
  have hgb := g.hom.naturality (b.hom.app M)
  have hgd := g.hom.naturality (H.map (d.app (Q.obj M)))
  dsimp only [Functor.comp_map] at hgb hgd
  rw [reassoc_of% hgd, reassoc_of% hgb]
  have hb := ub.inv.naturality (d.app (Q.obj M))
  dsimp only [Functor.comp_map, Functor.id_map] at hb
  simp only [← L.map_comp_assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj] at hb
  rw [hb]
  simp only [L.map_comp, hd, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem cancel_factorization_word {D : Type*} [Category D]
    {O X Y Z U V : D} (a : O ≅ X) (b : O ≅ Y) (c : Y ≅ Z)
    (d : O ≅ U) (e : U ≅ Z) (f : U ≅ V) (g : X ≅ V)
    (σ : X ⟶ Y) (τ : Z ⟶ V)
    (hσ : σ = a.inv ≫ b.hom) (hτ : τ = e.inv ≫ f.hom)
    (h₁ : d.hom ≫ e.hom = b.hom ≫ c.hom)
    (h₂ : d.hom ≫ f.hom = a.hom ≫ g.hom) :
    σ ≫ c.hom ≫ τ = g.hom := by
  rw [hσ, hτ]
  simp only [Category.assoc]
  rw [← reassoc_of% h₁]
  simp only [Iso.hom_inv_id_assoc]
  rw [h₂]
  simp only [Iso.inv_hom_id_assoc]

private theorem restriction_normalization_word
    {A C D E T : Type*} [Category A] [Category C] [Category D]
    [Category E] [Category T]
    (I : A ⥤ T) (Pi : T ⥤ A) (P : T ⥤ C) (Q : A ⥤ D)
    (L : D ⥤ E) (U : E ⥤ D) (H : D ⥤ C) (V : C ⥤ D)
    (K : E ⥤ C) (R : A ⥤ E) (Pk : C ⥤ E)
    (b : I ⋙ P ≅ Q ⋙ H) (d : 𝟭 D ⟶ L ⋙ U) (α : I ⋙ P ⟶ R ⋙ K)
    (σ : Pi ⋙ R ≅ P ⋙ Pk) (τ : P ⋙ V ≅ Pi ⋙ Q)
    (g : Pk ≅ V ⋙ L) (j : U ⋙ H ≅ K) (c : R ≅ Q ⋙ L)
    (us : 𝟭 E ≅ U ⋙ L) (ub : 𝟭 D ≅ H ⋙ V) (uk : 𝟭 E ≅ K ⋙ Pk)
    (ui : 𝟭 A ≅ I ⋙ Pi)
    (hd : ∀ N, L.map (d.app N) = us.hom.app (L.obj N))
    (hj : ∀ N, uk.hom.app N ≫ g.hom.app (K.obj N) =
      us.hom.app N ≫ L.map (ub.hom.app (U.obj N)) ≫ L.map (V.map (j.hom.app N)))
    (hb : ∀ N, V.map (b.hom.app N) ≫ ub.inv.app (Q.obj N) =
      τ.hom.app (I.obj N) ≫ Q.map (ui.inv.app N))
    (hs : ∀ N, σ.hom.app N ≫ g.hom.app (P.obj N) ≫ L.map (τ.hom.app N) =
      c.hom.app (Pi.obj N))
    (ha : ∀ N, α.app N = b.hom.app N ≫ H.map (d.app (Q.obj N)) ≫
      j.hom.app (L.obj (Q.obj N)) ≫ K.map (c.inv.app N)) (M : A) :
    σ.hom.app (I.obj M) ≫ Pk.map (α.app M) =
      R.map (ui.inv.app M) ≫ uk.hom.app (R.obj M) := by
  have hj' := unit_composite_restriction L U H V K Pk g j us ub uk hj
  have he := projector_restriction_word (I ⋙ P) Q L U H V K R Pk
    b d g j c us ub uk hd hj' M
  have he' : Pk.map (α.app M) ≫ uk.inv.app (R.obj M) =
      g.hom.app (P.obj (I.obj M)) ≫
        L.map (V.map (b.hom.app M) ≫ ub.inv.app (Q.obj M)) ≫ c.inv.app M :=
    (congrArg (fun f : P.obj (I.obj M) ⟶ K.obj (R.obj M) ↦
      Pk.map f ≫ uk.inv.app (R.obj M)) (ha M)).trans he
  apply (Iso.cancel_iso_hom_right _ _ (uk.symm.app (R.obj M))).1
  simp only [Iso.app_hom, Iso.symm_hom, Category.assoc]
  rw [he', hb, L.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hs (I.obj M)]
  have hn := c.hom.naturality (ui.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app, Functor.id_obj, Category.comp_id]

end AlgebraicGeometry.ProEtale.StrictTower
