/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal

/-! # Continuity of cartesian higher direct images with varying bases

Source: Stacks Project, Tag 0EYM.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The derived direct image on the cartesian pullback of `f` along `g`.
Source: Stacks Project, Tag 0EYM.
(blueprint: def-sc-cartesian-derived-image). -/
noncomputable abbrev cartesianDerivedImage {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S)
    (P : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (R+((pullback.snd f g)_*[AddCommGrpCat.{u + 1}])).obj
    ((D+((pullback.fst f g)^*[AddCommGrpCat.{u + 1}])).obj P)

/-- The canonical projection between two cartesian pullbacks.
Source: Stacks Project, Tag 0EYM.
(blueprint: def-sc-cartesian-image-projection). -/
noncomputable def cartesianImageProjection {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (a : T' ⟶ T) (w : g' = a ≫ g) :
    pullback f g' ⟶ pullback f g :=
  pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ a) (by
    rw [Category.assoc, ← w, pullback.condition])

/-- First projection equation of the canonical cartesian projection.
Source: the universal property of a pullback (Stacks Project, Tag 0EYM).
(blueprint: lem-sc-cartesian-image-projection-fst). -/
@[simp] theorem cartesianImageProjection_fst {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (a : T' ⟶ T) (w : g' = a ≫ g) :
    cartesianImageProjection f g g' a w ≫ pullback.fst f g = pullback.fst f g' :=
  pullback.lift_fst _ _ _

/-- Second projection equation of the canonical cartesian projection.
Source: the universal property of a pullback (Stacks Project, Tag 0EYM).
(blueprint: lem-sc-cartesian-image-projection-snd). -/
@[simp] theorem cartesianImageProjection_snd {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (a : T' ⟶ T) (w : g' = a ≫ g) :
    cartesianImageProjection f g g' a w ≫ pullback.snd f g = pullback.snd f g' ≫ a :=
  pullback.lift_snd _ _ _

/-- Exchange for a projection, followed by the inverse-image composition identification.
Source: Stacks Project, Tag 0EYM, construction of the comparison maps.
(blueprint: def-sc-cartesian-derived-image-map). -/
noncomputable def cartesianDerivedImageMap {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (a : T' ⟶ T) (w : g' = a ≫ g)
    (P : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (D+((a)^*[AddCommGrpCat.{u + 1}])).obj (cartesianDerivedImage f g P) ⟶
      cartesianDerivedImage f g' P :=
  (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (show CommSq (cartesianImageProjection f g g' a w) (pullback.snd f g')
        (pullback.snd f g) a from ⟨by simp⟩)).app
        ((D+((pullback.fst f g)^*[AddCommGrpCat.{u + 1}])).obj P) ≫
    (R+((pullback.snd f g')_*[AddCommGrpCat.{u + 1}])).map
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
        (cartesianImageProjection f g g' a w) (pullback.fst f g)
        (pullback.fst f g') (cartesianImageProjection_fst f g g' a w).symm).inv.app P)

private theorem derivedExchange_transport
    {S T X Y : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T}
    {a a' : T ⟶ S} {b b' : Y ⟶ X}
    (sq : CommSq b f' f a) (sq' : CommSq b' f' f a')
    (ha : a = a') (hb : b = b')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    eqToHom (congrArg (fun c ↦ (D+((c)^*[AddCommGrpCat.{u + 1}])).obj
        ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj K)) ha) ≫
      (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq').app K =
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K ≫
      (R+((f')_*[AddCommGrpCat.{u + 1}])).map
        (eqToHom (congrArg (fun c ↦ (D+((c)^*[AddCommGrpCat.{u + 1}])).obj K) hb)) := by
  subst a' b'
  simp

private theorem upperStarComp_inv_transport {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (d d' : X ⟶ Z)
    (hd : d = a ≫ b) (hd' : d' = a ≫ b) (h : d = d')
    (P : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a b d hd).inv.app P =
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a b d' hd').inv.app P ≫
        eqToHom (congrArg
          (fun c ↦ (D+((c)^*[AddCommGrpCat.{u + 1}])).obj P) h.symm) := by
  cases h
  rw [eqToHom_refl, Category.comp_id]

/-- Pasting identifies the transition of a stage exchange with the later exchange.
Source: Stacks Project, Tag 0EYM, compatibility of the comparison maps.
(blueprint: lem-sc-cartesian-derived-image-map-exchange). -/
theorem cartesianDerivedImageMap_exchange {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (a : T' ⟶ T) (w : g' = a ≫ g)
    (P : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a g g' w).hom.app
        ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj P) ≫
      (D+((a)^*[AddCommGrpCat.{u + 1}])).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
          (IsPullback.of_hasPullback f g).toCommSq).app P) ≫
      cartesianDerivedImageMap f g g' a w P =
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (IsPullback.of_hasPullback f g').toCommSq).app P := by
  subst g'
  let b := cartesianImageProjection f g (a ≫ g) a rfl
  let sq₂ : CommSq b (pullback.snd f (a ≫ g)) (pullback.snd f g) a := ⟨by simp [b]⟩
  let sq : CommSq (b ≫ pullback.fst f g) (pullback.snd f (a ≫ g)) f (a ≫ g) :=
    ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, sq₂.w, Category.assoc]⟩
  have hp := NatTrans.congr_app (derivedBaseChangeMapPlus_paste_horiz
    AddCommGrpCat.{u + 1} (IsPullback.of_hasPullback f g).toCommSq sq₂ sq) P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp] at hp
  have ht := derivedExchange_transport sq (IsPullback.of_hasPullback f (a ≫ g)).toCommSq
    rfl (cartesianImageProjection_fst f g (a ≫ g) a rfl) P
  rw [hp] at ht
  simp only [eqToHom_refl, Category.id_comp] at ht
  dsimp only [cartesianDerivedImageMap]
  rw [upperStarComp_inv_transport b (pullback.fst f g) (pullback.fst f (a ≫ g))
    (b ≫ pullback.fst f g) (cartesianImageProjection_fst f g (a ≫ g) a rfl).symm
    rfl (cartesianImageProjection_fst f g (a ≫ g) a rfl).symm P]
  rw [Functor.map_comp]
  simpa only [Category.assoc] using ht.symm

/-- A pulled-back stage higher image, computed by bounded-below derived homology.
Source: Stacks Project, Tag 0EYM.
(blueprint: def-sc-cartesian-higher-image-stage). -/
noncomputable abbrev cartesianHigherImageStage {X S : Scheme.{u}} {I : Type u}
    [SmallCategory I] (D : I ⥤ Over S) (c : Cone D) (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (i : I) :
    Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
    ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
      (cartesianDerivedImage f (D.obj i).hom
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))

/-- The higher image on the limit base.
Source: Stacks Project, Tag 0EYM.
(blueprint: def-sc-cartesian-higher-image-limit). -/
noncomputable abbrev cartesianHigherImageLimit {X S : Scheme.{u}} {I : Type u}
    [SmallCategory I] (D : I ⥤ Over S) (c : Cone D) (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
    (cartesianDerivedImage f c.pt.hom ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- The canonical map from a stage higher image to the limit higher image.
Source: Stacks Project, Tag 0EYM.
(blueprint: def-sc-cartesian-higher-image-leg). -/
noncomputable def cartesianHigherImageLeg {X S : Scheme.{u}} {I : Type u}
    [SmallCategory I] (D : I ⥤ Over S) (c : Cone D) (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (i : I) :
    cartesianHigherImageStage D c f F q i ⟶ cartesianHigherImageLimit D c f F q :=
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    (cartesianDerivedImageMap f (D.obj i).hom c.pt.hom (c.π.app i).left
      (Over.w (c.π.app i)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- The stage transition on the limit base, with its inverse-image composition transport.
Source: Stacks Project, Tag 0EYM.
(blueprint: def-sc-cartesian-higher-image-transition). -/
noncomputable def cartesianHigherImageTransition {X S : Scheme.{u}} {I : Type u}
    [SmallCategory I] (D : I ⥤ Over S) (c : Cone D) (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {i j : I} (a : j ⟶ i) :
    cartesianHigherImageStage D c f F q i ⟶ cartesianHigherImageStage D c f F q j :=
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (c.π.app j).left (D.map a).left
        (c.π.app i).left (congrArg (fun b ↦ b.left) (c.w a)).symm).hom.app _ ≫
      (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).map
        (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom (D.map a).left
          (Over.w (D.map a)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))

end AlgebraicGeometry.Etale
