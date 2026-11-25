/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageCoreComp

/-! # Composition of abelian higher direct image transitions
Source: Stacks Project, Tag 09Z1, canonical cohomology comparison maps. -/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem map_coefficient_comp {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' G' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F') (ψ : F' ⟶ G') :
    abelianHigherDirectImageMap a h h' w p F G' (φ ≫ ψ) =
      abelianHigherDirectImageMap a h h' w p F F' φ ≫
        (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
          (R+((h')_*[AddCommGrpCat.{v + 1}]).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map ψ)) := by
  simp only [abelianHigherDirectImageMap, Functor.map_comp, Category.assoc]

private theorem map_coefficient_naturality {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) (ψ : F ⟶ G) :
    (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
        (R+((h)_*[AddCommGrpCat.{v + 1}]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ψ)) ≫
      abelianHigherDirectImageMap a h h' w p G
        (((a)^*[AddCommGrpCat.{v + 1}]).obj G) (𝟙 _) =
    abelianHigherDirectImageMap a h h' w p F
        (((a)^*[AddCommGrpCat.{v + 1}]).obj F) (𝟙 _) ≫
      (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
        (R+((h')_*[AddCommGrpCat.{v + 1}]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            (((a)^*[AddCommGrpCat.{v + 1}]).map ψ))) := by
  subst h'
  let A := AddCommGrpCat.{v + 1}
  let Rh := R+((h)_*[A])
  let Rh' := R+((a ≫ h)_*[A])
  let La := D+((a)^*[A])
  let c : D+((a ≫ h)^*[A]) ≅ D+((h)^*[A]) ⋙ La :=
    eqToIso (by rfl) ≪≫ upperStarPlusComp A a h
  let adj := (upperStarLowerStarAdjunction A h).derivedPlus
  let adj' := (upperStarLowerStarAdjunction A (a ≫ h)).derivedPlus
  let t : Rh ⟶ La ⋙ Rh' :=
    Functor.whiskerLeft Rh adj'.unit ≫
      Functor.whiskerRight (Functor.whiskerLeft Rh c.hom ≫ Functor.whiskerRight adj.counit La) Rh'
  let single := DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology A) 0
  let comparison := (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom
  let coefficient := Functor.whiskerLeft single t ≫ Functor.whiskerRight comparison Rh'
  let transition := Functor.whiskerRight coefficient
    (DerivedCategory.Plus.homologyFunctor _ (p : ℤ))
  have hc := transition.naturality ψ
  simp only [abelianHigherDirectImageMap, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  erw [(DerivedCategory.Plus.singleFunctor _ 0).map_id,
    (DerivedCategory.Plus.singleFunctor _ 0).map_id]
  simp only [Category.assoc, ← Functor.map_comp]
  erw [Category.comp_id, Category.id_comp]
  simpa only [transition, coefficient, comparison, single, t,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app, Functor.comp_map,
    c, eqToIso_refl, Iso.refl_trans, Category.assoc, Category.comp_id,
    ← Functor.map_comp] using hc

private theorem map_comp {S Y Y' Y'' : Scheme.{v}}
    (a : Y' ⟶ Y) (b : Y'' ⟶ Y') (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Y'' ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F'' : Sheaf Y''.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F')
    (ψ : ((b)^*[AddCommGrpCat.{v + 1}]).obj F' ⟶ F'') :
    abelianHigherDirectImageMap (b ≫ a) h h''
        (by rw [Category.assoc, wa, wb]) p F F''
        ((upperStarComp AddCommGrpCat.{v + 1} b a).hom.app F ≫
          ((b)^*[AddCommGrpCat.{v + 1}]).map φ ≫ ψ) =
      abelianHigherDirectImageMap a h h' wa p F F' φ ≫
        abelianHigherDirectImageMap b h' h'' wb p F' F'' ψ := by
  have ha := map_coefficient_comp a h h' wa p F
    (((a)^*[AddCommGrpCat.{v + 1}]).obj F) F' (𝟙 _) φ
  simp only [Category.id_comp] at ha
  have hb := map_coefficient_comp b h' h'' wb p F'
    (((b)^*[AddCommGrpCat.{v + 1}]).obj F') F'' (𝟙 _) ψ
  simp only [Category.id_comp] at hb
  rw [ha, hb]
  simp only [← Category.assoc]
  rw [Category.assoc (abelianHigherDirectImageMap a h h' wa p F
    (((a)^*[AddCommGrpCat.{v + 1}]).obj F) (𝟙 _)),
    map_coefficient_naturality b h' h'' wb p _ F' φ]
  simp only [← Category.assoc]
  rw [← abelianHigherDirectImage_core_comp a b h h' h'' wa wb p F]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← map_coefficient_comp]

private theorem map_transport {S Y Y' : Scheme.{v}}
    (a a' : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S)
    (w : a ≫ h = h') (w' : a' ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F')
    (φ' : ((a')^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F')
    (ha : a = a') (hφ : HEq φ φ') :
    abelianHigherDirectImageMap a h h' w p F F' φ =
      abelianHigherDirectImageMap a' h h' w' p F F' φ' := by
  subst a'
  cases eq_of_heq hφ
  rfl

/-- Canonical abelian higher direct image transitions respect coefficient composition.
Source: Stacks Project, Tag 09Z1, functoriality of the comparison maps.
(blueprint: lem-sbc-abelian-higher-direct-image-transition-comp).

Proof: Expand both transitions before degree-p homology. Naturality moves the
second derived adjunction unit past the first coefficient map. The triangle
identity cancels the intermediate counit with that unit. The associativity
coherence of inverse-image composition and its comparison with the single
functor identifies the remaining factors with the transition for f followed
by g. Substitute hφcomp and D.map_comp (in the opposite order). Apply the
homology functor, which preserves composition. Identity and structure-map
proof transports agree by proof irrelevance. No limit or qcqs hypothesis is used.
This also applies when a stage or sheaf is zero. -/
theorem abelianHigherDirectImage_transition_comp {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (p : ℕ) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    abelianHigherDirectImageMap (D.map (f ≫ g).op).left (D.obj (op i)).hom
        (D.obj (op k)).hom (Over.w (D.map (f ≫ g).op)) p (F i) (F k) (φ (f ≫ g)) =
      abelianHigherDirectImageMap (D.map f.op).left (D.obj (op i)).hom
          (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f) ≫
        abelianHigherDirectImageMap (D.map g.op).left (D.obj (op j)).hom
          (D.obj (op k)).hom (Over.w (D.map g.op)) p (F j) (F k) (φ g) := by
  have _ := hφid i
  have hd : (D.map (f ≫ g).op).left = (D.map g.op).left ≫ (D.map f.op).left := by
    simp only [op_comp, Functor.map_comp, Over.comp_left]
  have wcomp : ((D.map g.op).left ≫ (D.map f.op).left) ≫ (D.obj (op i)).hom =
      (D.obj (op k)).hom := by
    rw [Category.assoc, Over.w (D.map f.op), Over.w (D.map g.op)]
  refine (map_transport (D.map (f ≫ g).op).left
    ((D.map g.op).left ≫ (D.map f.op).left) (D.obj (op i)).hom (D.obj (op k)).hom
    (Over.w (D.map (f ≫ g).op)) wcomp p (F i) (F k) (φ (f ≫ g))
    ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
      (D.map f.op).left).hom.app (F i) ≫
      (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g)
    hd (hφcomp f g)).trans ?_
  exact map_comp (D.map f.op).left (D.map g.op).left (D.obj (op i)).hom
    (D.obj (op j)).hom (D.obj (op k)).hom (Over.w (D.map f.op))
    (Over.w (D.map g.op)) p (F i) (F j) (F k) (φ f) (φ g)

end AlgebraicGeometry.Etale
