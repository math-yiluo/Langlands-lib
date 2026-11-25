/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Comap
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!

# Germs and the inverse image of a point along a continuous functor

Let `F : C ⥤ D` be a representably flat, cover preserving and continuous functor between
sites `(C, J)` and `(D, K)` and let `Φ` be a point of `(D, K)`. Mathlib's
`CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` identifies the fibre functor
on sheaves of the point `Φ.comap F hF` of `(C, J)` with the sheaf pullback along `F`
followed by the fibre functor of `Φ`. It is defined as a conjugate (a mate) of the identity
of the skyscraper functors, so nothing describes it on germs. This file supplies that
description.

## Main results

- `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app`:
  on the germ at a pointed object `(X, x)` of the site `(C, J)`, the isomorphism
  `sheafFiberComapIso` is the unit of the adjunction `F^* ⊣ F_*` followed by the germ map of
  `Φ` at `(F X, x)`.
- `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_counit`:
  consequently the germ map of `Φ.comap F hF` at `(X, x)`, followed by `sheafFiberComapIso`
  and by the fibre of the counit of `F^* ⊣ F_*`, is the germ map of `Φ` at `(F X, x)`.

-/

@[expose] public section

universe w v' u'

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C D : Type*} [Category* C] [Category* D]
  {K : GrothendieckTopology D}
  (Φ : Point.{w} K) (F : C ⥤ D) [RepresentablyFlat F] {J : GrothendieckTopology C}
  (hF : CoverPreserving J K F)
  [InitiallySmall (F ⋙ Φ.fiber).Elements]
  (A : Type u') [Category.{v'} A] [HasProducts.{w} A]
  [Functor.IsContinuous F J K]
  [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasColimitsOfSize.{w, w} A]

/-- The germ description of
`CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso`: composing the germ map of
the point `Φ.comap F hF` at a pointed object `(X, x)` with the comparison isomorphism gives
the unit of the adjunction `F^* ⊣ F_*` followed by the germ map of `Φ` at `(F X, x)`. -/
@[reassoc]
lemma toPresheafFiber_sheafFiberComapIso_hom_app (G : Sheaf J A) (X : C)
    (x : Φ.fiber.obj (F.obj X)) :
    (Φ.comap F hF).toPresheafFiber X x G.obj ≫ (Φ.sheafFiberComapIso F hF A).hom.app G =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) x ((F.sheafPullback A J K).obj G).obj := by
  have h0 := unit_conjugateEquiv_symm
    ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
    ((Φ.comap F hF).skyscraperSheafAdjunction)
    (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous F hF A).hom G
  simp only [skyscraperSheafFunctorCompSheafPushforwardContinuous, Iso.refl_hom] at h0
  have key : (Φ.sheafFiberComapIso F hF A).hom =
      (conjugateEquiv ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
        ((Φ.comap F hF).skyscraperSheafAdjunction)).symm (𝟙 _) := rfl
  rw [key]
  set Θ := (conjugateEquiv ((F.sheafAdjunctionContinuous A J K).comp
    Φ.skyscraperSheafAdjunction) ((Φ.comap F hF).skyscraperSheafAdjunction)).symm (𝟙 _)
  have h2 : ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        (Φ.skyscraperSheafAdjunction.unit.app ((F.sheafPullback A J K).obj G)).hom.app
            (op (F.obj X)) ≫
          Limits.Pi.π (fun _ : (Φ.comap F hF).fiber.obj X ↦
            Φ.sheafFiber.obj ((F.sheafPullback A J K).obj G)) x =
      (Φ.comap F hF).toPresheafFiber X x G.obj ≫ Θ.app G := by
    simpa using (NatTrans.congr_app (Sheaf.hom_ext_iff.1 h0) (op X)) =≫ Limits.Pi.π _ x
  rw [← h2]
  congr 1
  exact Φ.skyscraperSheafAdjunction_unit_app_hom_app_π _ _ _

/-- The germ map of `Φ.comap F hF` at a pointed object `(X, x)`, followed by the comparison
isomorphism `CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` and by the fibre
of the counit of `F^* ⊣ F_*`, is the germ map of `Φ` at `(F X, x)`. -/
@[reassoc]
lemma toPresheafFiber_sheafFiberComapIso_hom_app_counit (E : Sheaf K A) (X : C)
    (x : Φ.fiber.obj (F.obj X)) :
    (Φ.comap F hF).toPresheafFiber X x
          ((F.sheafPushforwardContinuous A J K).obj E).obj ≫
        (Φ.sheafFiberComapIso F hF A).hom.app ((F.sheafPushforwardContinuous A J K).obj E) ≫
        Φ.sheafFiber.map ((F.sheafAdjunctionContinuous A J K).counit.app E) =
      Φ.toPresheafFiber (F.obj X) x E.obj := by
  rw [toPresheafFiber_sheafFiberComapIso_hom_app_assoc,
    show Φ.sheafFiber.map ((F.sheafAdjunctionContinuous A J K).counit.app E) =
    Φ.presheafFiber.map ((F.sheafAdjunctionContinuous A J K).counit.app E).hom from rfl,
    toPresheafFiber_naturality]
  have ht : ((F.sheafAdjunctionContinuous A J K).unit.app
        ((F.sheafPushforwardContinuous A J K).obj E)).hom.app (op X) ≫
      ((F.sheafAdjunctionContinuous A J K).counit.app E).hom.app (op (F.obj X)) =
      𝟙 (E.obj.obj (op (F.obj X))) :=
    NatTrans.congr_app (Sheaf.hom_ext_iff.1
      ((F.sheafAdjunctionContinuous A J K).right_triangle_components E)) (op X)
  rw [← Category.assoc, ht]
  exact Category.id_comp _

end CategoryTheory.GrothendieckTopology.Point
