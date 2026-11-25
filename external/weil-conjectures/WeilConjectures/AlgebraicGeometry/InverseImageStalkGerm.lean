/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Stalk of an inverse image, compatible with germs of pulled-back sections

Source: literature/stacks-project/etale-cohomology.tex, Lemma Tag 03Q1 (3)
(blueprint: lem-weil-pbc-inverse-image-stalk-germ).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry

/-- **Stalk of an inverse image, compatible with germs.** Let `f : Y ⟶ X` be a morphism of
schemes, `y : Spec Ω ⟶ Y` a geometric point and `x̄ = y ≫ f`. There is an isomorphism
`c_G : (f⁻¹ G)_ȳ ≅ G_x̄`, natural in the abelian étale sheaf `G`, such that for every pointed
étale neighbourhood `(U, ū)` of `x̄` and every section `a ∈ G(U)`, `c_G` sends the germ of
`η_{f,G}(U)(a) ∈ (f⁻¹G)(U ×_X Y)` at the induced pointed neighbourhood `(U ×_X Y, (ū, ȳ))`
of `ȳ` to the germ of `a` at `(U, ū)`. Here `f⁻¹ = Etale.upperStar`, `η` is the unit of
`Etale.upperStarLowerStarAdjunction`, stalks and germs are `pointSmallEtale`'s
`sheafFiber`/`toPresheafFiber`, and `(ū, ȳ)` is `(pointSmallEtaleFiberEtaleIso f y).inv`.

Proof: take `Etale.upperStarCompSheafFiberIso`, the general-site identification of
pullback stalks transported along `pointSmallEtaleComapIso`. To check the germ formula,
compose with its inverse and expand its three factors. The germ formula for an
isomorphism of points transports `ū` to `(pointSmallEtaleFiberEtaleIso f y).inv.app U ū`.
The germ formula for `sheafFiberComapIso` gives the unit of the abstract sheaf pullback.
Move the comparison with the constructed pullback past the germ map by naturality;
`Adjunction.unit_leftAdjointUniq_hom_app` identifies the resulting composite with the
unit of `Etale.upperStarLowerStarAdjunction`. Naturality in `G` is already part of the
chosen natural isomorphism. This is the general-site route of Stacks Tag 03Q1 (3),
which cites Sites Tag 05V1, rather than its alternative direct colimit computation.

Source: literature/stacks-project/etale-cohomology.tex, Lemma Tag 03Q1 (3)
(blueprint: lem-weil-pbc-inverse-image-stalk-germ). -/
theorem inverseImage_stalk_germ
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    ∃ c : Etale.upperStar AddCommGrpCat.{u + 1} f ⋙ (pointSmallEtale y).sheafFiber ≅
        (pointSmallEtale (y ≫ f)).sheafFiber,
      ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Etale)
        (ū : (pointSmallEtale (y ≫ f)).fiber.obj U),
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app
              (op U) ≫
            (pointSmallEtale y).toPresheafFiber (f.Etale.obj U)
              ((pointSmallEtaleFiberEtaleIso f y).inv.app U ū)
              ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G).obj ≫
            (c.app G).hom =
          (pointSmallEtale (y ≫ f)).toPresheafFiber U ū G.obj := by
  refine ⟨Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f y, ?_⟩
  intro G U ū
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv _).1
  simp only [Etale.upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [show (pointSmallEtale y).sheafFiber.map _ =
    (pointSmallEtale y).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) AddCommGrpCat.{u + 1}
      (X.smallGrothendieckTopology (P := @Etale))
      (Y.smallGrothendieckTopology (P := @Etale)))
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  rw [← Category.assoc, ← huU]
  rfl

end AlgebraicGeometry
