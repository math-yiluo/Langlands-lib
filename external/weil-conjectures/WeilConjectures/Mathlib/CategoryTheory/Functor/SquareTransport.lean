/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!

# Transport of a natural isomorphism under outer functors

A natural isomorphism `θ : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄` is transported under `R` on the left and `R'`
on the right (with the reassociations) to
`(R ⋙ G₁) ⋙ (G₂ ⋙ R') ≅ (R ⋙ G₃) ⋙ (G₄ ⋙ R')`, whose component at `K` is
`R'.mapIso (θ.app (R.obj K))`. This is the square-transport step of the base-change morphisms
of the six-functor formalisms, see
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`.

## Main definitions

- `CategoryTheory.Functor.squareTransport`, with its component lemmas `squareTransport_hom_app`,
  `squareTransport_inv_app` and `squareTransport_app`.

-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C₁ C₂ C₃ C₃' C₄ C₅ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₃'] [Category* C₄] [Category* C₅]
  {G₁ : C₂ ⥤ C₃} {G₂ : C₃ ⥤ C₄} {G₃ : C₂ ⥤ C₃'} {G₄ : C₃' ⥤ C₄}

/-- Transport of a natural isomorphism `θ : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄` under `R` on the left and
`R'` on the right: the natural isomorphism
`(R ⋙ G₁) ⋙ (G₂ ⋙ R') ≅ (R ⋙ G₃) ⋙ (G₄ ⋙ R')` obtained by whiskering `θ` and
reassociating. Its component at `K` is `R'.mapIso (θ.app (R.obj K))`, see
`Functor.squareTransport_app`. -/
def squareTransport (R : C₁ ⥤ C₂) (R' : C₄ ⥤ C₅) (θ : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄) :
    (R ⋙ G₁) ⋙ (G₂ ⋙ R') ≅ (R ⋙ G₃) ⋙ (G₄ ⋙ R') :=
  associator R G₁ (G₂ ⋙ R') ≪≫ isoWhiskerLeft R
    ((associator G₁ G₂ R').symm ≪≫ isoWhiskerRight θ R' ≪≫ associator G₃ G₄ R') ≪≫
      (associator R G₃ (G₄ ⋙ R')).symm

variable (R : C₁ ⥤ C₂) (R' : C₄ ⥤ C₅) (θ : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄) (K : C₁)

@[simp]
lemma squareTransport_hom_app :
    (squareTransport R R' θ).hom.app K = R'.map (θ.hom.app (R.obj K)) := by
  simp [squareTransport]

@[simp]
lemma squareTransport_inv_app :
    (squareTransport R R' θ).inv.app K = R'.map (θ.inv.app (R.obj K)) := by
  simp [squareTransport]

@[simp]
lemma squareTransport_app :
    (squareTransport R R' θ).app K = R'.mapIso (θ.app (R.obj K)) := by
  ext
  simp

end CategoryTheory.Functor
