/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Module inverse image and underlying abelian sheaves

Source: Stacks Project, Modules on Sites, Lemmas 03D2 and 03D3.
(blueprint: lem-weil-pbc-module-abelian-inverse-image-comparison) -/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The mate of the underlying module adjunction unit is an isomorphism.

Source: Stacks Project, Modules on Sites, Lemmas 03D2 and 03D3.
(blueprint: lem-weil-pbc-module-abelian-inverse-image-comparison)

Proof:
1. The forgetful functor from modules to abelian groups preserves colimits and
limits, hence it commutes with left Kan extension and sheafification. Compose
Mathlib's inverse Kan-extension comparison with its sheafification comparison
`sheafComposeNatIso` to obtain an isomorphism from abelian inverse image of the
underlying sheaf to the underlying module inverse image.
2. Its composite with the abelian sheafification unit is the inverse
Kan-extension comparison followed by the underlying module sheafification unit.
This follows from naturality of the sheafification unit and
`sheafComposeNatTrans_fac`.
3. The unit factorization of `leftKanExtensionCompIsoOfPreserves` now identifies
the adjoint of this isomorphism with the underlying module adjunction unit.
Injectivity of the abelian adjunction bijection identifies its forward map with
the displayed canonical map, which is therefore an isomorphism. -/
theorem isIso_moduleAbelianInverseImageComparison
    {X Y : Scheme.{u}} (i : X ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv
      ((sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J)
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((i)^*[ModuleCat.{u + 1} Λ].obj J))).symm
      ((sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app J))) := by
  let G := (MorphismProperty.Over.pullback @Etale ⊤ i).op
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : X.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification _ _
  let e := (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
      (U.leftKanExtensionCompIsoOfPreserves J.obj G).symm ≪≫
    (sheafComposeNatIso X.smallEtaleTopology U
      (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
        (G.lan.obj J.obj)
  have hm : ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app J).hom =
      ((G.lanAdjunction (ModuleCat.{u + 1} Λ)).comp
        (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).unit.app
          J.obj := by
    change (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app J) = _
    dsimp only [upperStarLowerStarAdjunction,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp [G]
    rfl
  have ha : ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app
      ((sheafCompose Y.smallEtaleTopology U).obj J)).hom =
      ((G.lanAdjunction AddCommGrpCat.{u + 1}).comp
        (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).unit.app
          ((sheafCompose Y.smallEtaleTopology U).obj J).obj := by
    change (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app
        ((sheafCompose Y.smallEtaleTopology U).obj J)) = _
    dsimp only [upperStarLowerStarAdjunction,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp [G]
    rfl
  have hf : toSheafify X.smallEtaleTopology (G.lan.obj (J.obj ⋙ U)) ≫ e.hom.hom =
      (U.leftKanExtensionCompIsoOfPreserves J.obj G).inv ≫
        Functor.whiskerRight (toSheafify X.smallEtaleTopology (G.lan.obj J.obj)) U := by
    change (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app
      (G.lan.obj (J.obj ⋙ U)) ≫
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (U.leftKanExtensionCompIsoOfPreserves J.obj G).inv ≫
          (sheafComposeNatTrans X.smallEtaleTopology U
            (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
            (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
              (G.lan.obj J.obj)) = _
    rw [Functor.map_comp, ← Category.assoc]
    erw [← (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.naturality]
    rw [Category.assoc]
    erw [sheafComposeNatTrans_fac]
    rfl
  have he : e.hom =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv
        ((sheafCompose Y.smallEtaleTopology U).obj J)
        ((sheafCompose X.smallEtaleTopology U).obj ((i)^*[ModuleCat.{u + 1} Λ].obj J))).symm
          ((sheafCompose Y.smallEtaleTopology U).map
            ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app J)) := by
    apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv
      ((sheafCompose Y.smallEtaleTopology U).obj J)
      ((sheafCompose X.smallEtaleTopology U).obj ((i)^*[ModuleCat.{u + 1} Λ].obj J))
      |>.injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    apply (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map_injective
    change ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app
      ((sheafCompose Y.smallEtaleTopology U).obj J)).hom ≫
        Functor.whiskerLeft G e.hom.hom =
      Functor.whiskerRight
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app J).hom U
    rw [hm, ha]
    simp only [Adjunction.comp_unit_app]
    change (G.lanUnit.app (J.obj ⋙ U) ≫
      Functor.whiskerLeft G (toSheafify X.smallEtaleTopology (G.lan.obj (J.obj ⋙ U)))) ≫
        Functor.whiskerLeft G e.hom.hom =
      Functor.whiskerRight (G.lanUnit.app J.obj ≫
        Functor.whiskerLeft G (toSheafify X.smallEtaleTopology (G.lan.obj J.obj))) U
    rw [Category.assoc, ← Functor.whiskerLeft_comp, hf, Functor.whiskerLeft_comp,
      ← Category.assoc]
    erw [Functor.leftKanExtensionCompIsoOfPreserves_inv_fac]
    ext W
    simp
    rfl
  rw [← he]
  infer_instance

end AlgebraicGeometry.Etale
