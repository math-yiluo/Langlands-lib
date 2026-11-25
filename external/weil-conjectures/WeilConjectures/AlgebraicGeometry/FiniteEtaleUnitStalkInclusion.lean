/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

/-!
# The finite étale reverse-adjunction unit on geometric stalks

Source: Stacks Project, Section 03SH and Lemma 03S7, via the extension by zero
construction of the reverse adjunction in `UpperLowerStar.FiniteEtale`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Etale

private theorem pullback_unit_germ
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R] (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (U : X.Etale)
    (v : (Scheme.pointSmallEtale (t ≫ f)).fiber.obj U) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G).hom.app
        (op U) ≫
      (Scheme.pointSmallEtale t).toPresheafFiber (f.Etale.obj U)
        ((Scheme.pointSmallEtaleFiberEtaleIso f t).inv.app U v)
        ((f)^*[ModuleCat.{u + 1} R].obj G).obj ≫
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t).app G).hom =
    (Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber U v G.obj := by
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv _).1
  simp only [upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc,
    GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  erw [show (Scheme.pointSmallEtale t).sheafFiber.map _ =
    (Scheme.pointSmallEtale t).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (ModuleCat.{u + 1} R)
      (X.smallGrothendieckTopology (P := @Etale))
      (Y.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  erw [← Category.assoc, ← huU]
  rfl

private theorem localizationIso_inv_sections
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (U : Y.Etale) :
    ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} R) f inferInstance).inv.app
        G).hom.app (op U) =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G).hom.app
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj U)) ≫
        ((f)^*[ModuleCat.{u + 1} R].obj G).obj.map (Scheme.Etale.graph f U).op := by
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f
  let b := localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} R) f inferInstance
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app b a G
  rw [← Adjunction.leftAdjointUniq_inv_app] at h
  have he : (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} R) f
      inferInstance).inv.app G = (b.homEquiv _ _).symm (a.unit.app G) := by
    apply (b.homEquiv _ _).injective
    exact h.trans ((b.homEquiv _ _).apply_symm_apply _).symm
  rw [he, Adjunction.homEquiv_counit]
  change ((a.unit.app G).hom.app _) ≫ (b.counit.app _).hom.app (op U) = _
  erw [localizationRestrictionLowerStarAdjunction_counit_app_hom_app]
  rfl

/-- The unit of `f_* ⊣ f^*`, under the pullback stalk comparison, includes the stalk
at a lift into the corresponding summand of the pushforward stalk.

Source: Stacks Project, Section 03SH (trace as adjunction counit), Lemma 03S7
(`f_! = f_*` for finite étale maps), and the explicit extension by zero construction
in `WeilConjectures/SixFunctors/Etale/UpperLowerStar/FiniteEtale.lean`.
(blueprint: lem-weil-pbc-finite-etale-unit-stalk-inclusion)

Proof: The reverse adjunction is constructed from `lowerStarUnit`, whose section
on an étale `Y`-object `U` extends a section of `H(U)` by zero from the graph into
`U ×_X Y`. Its transport to `upperStar` uses the inverse of
`upperStarIsoLocalizationRestriction`. Fix a pointed neighbourhood `(U, x)` of
`t`. Under `upperStarCompSheafFiberIso`, the germ of this extension is the germ
at `s` over the localized object `U → Y → X`, at the point `x → U → X`.
To check this normalization, expand the stalk comparison into the constructed/
abstract pullback comparison, `sheafFiberComapIso`, and `pointSmallEtaleComapIso`;
apply `toPresheafFiber_sheafFiberComapIso_hom_app` and the unit compatibility of
`Adjunction.leftAdjointUniq`. The pullback point has components `(x, t)` and lies
on the graph. This gives exactly the maps used by `sheafFiberToLowerStar` to
construct its colimit descender. Equality on all such germs gives equality on
the stalk by `presheafFiber_hom_ext`. Finally transport along `t.2`. This argument
is coefficient-linear throughout, and uses no degree or nonempty-fibre assumption. -/
theorem finiteEtaleUnit_stalk_inclusion
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : f.GeometricFiber s) :
    (Scheme.pointSmallEtale t.1).sheafFiber.map
        ((lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).unit.app H) ≫
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t.1).app
        ((f)_*[ModuleCat.{u + 1} R].obj H)).hom ≫
      eqToHom (by rw [t.2]) =
    sheafFiberToLowerStar (ModuleCat.{u + 1} R) f t H := by
  obtain ⟨t, rfl⟩ := t
  simp only [eqToHom_refl, Category.comp_id]
  let A := ModuleCat.{u + 1} R
  have hu : (lowerStarUpperStarAdjunctionOfIsFinite A f).unit.app H =
      (lowerStarUnit A f).app H ≫
        (upperStarIsoLocalizationRestriction A f inferInstance).inv.app ((f)_*[A].obj H) := by
    simp only [lowerStarUpperStarAdjunctionOfIsFinite, Adjunction.ofNatIsoRight_unit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
      lowerStarLocalizationRestrictionAdjunction_unit]
  apply (Scheme.pointSmallEtale t).presheafFiber_hom_ext
  intro U x
  change (Scheme.pointSmallEtale t).toPresheafFiber U x H.obj ≫
      (Scheme.pointSmallEtale t).presheafFiber.map _ ≫ _ = _
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  change ((lowerStarUpperStarAdjunctionOfIsFinite A f).unit.app H).hom.app (op U) ≫
      (Scheme.pointSmallEtale t).toPresheafFiber U x
        ((f)^*[A].obj ((f)_*[A].obj H)).obj ≫
      ((upperStarCompSheafFiberIso A f t).app ((f)_*[A].obj H)).hom =
    (Scheme.pointSmallEtale t).toPresheafFiber U x H.obj ≫
      sheafFiberToLowerStar A f ⟨t, rfl⟩ H
  erw [toPresheafFiber_sheafFiberToLowerStar A f ⟨t, rfl⟩ H U x]
  rw [hu]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStarUnit_app_hom_app, Category.assoc]
  erw [localizationIso_inv_sections]
  let V := (MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj U
  let v := fiberMapPoint f ⟨t, rfl⟩ U x
  have hp : (Scheme.pointSmallEtaleFiberEtaleIso f t).inv.app V v =
      (Scheme.pointSmallEtale t).fiber.map (Scheme.Etale.graph f U) x := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply pullback.hom_ext
    · change _ = (x.left ≫ (Scheme.Etale.graph f U).left) ≫ _
      erw [Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst,
        Category.assoc, Scheme.Etale.graph_left_fst, Category.comp_id]
      rfl
    · change _ = (x.left ≫ (Scheme.Etale.graph f U).left) ≫ _
      erw [Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_snd,
        Category.assoc, Scheme.Etale.graph_left_snd]
      exact (CategoryTheory.Over.w x).symm
  have hg := pullback_unit_germ R f t ((f)_*[A].obj H) V v
  rw [hp] at hg
  have hw := (Scheme.pointSmallEtale t).toPresheafFiber_w (Scheme.Etale.graph f U) x
    ((f)^*[A].obj ((f)_*[A].obj H)).obj
  rw [← hw] at hg
  simpa only [Category.assoc] using congrArg (Scheme.Etale.graphExtend f H U ≫ ·) hg

end AlgebraicGeometry.Etale
