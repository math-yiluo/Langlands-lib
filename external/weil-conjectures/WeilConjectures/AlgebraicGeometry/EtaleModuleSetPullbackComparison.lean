/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # The canonical comparison of module and set inverse images

Source: Stacks Project, Tags 03D3 and 03D7, and the coefficient-forgetting
comparison in lem-sc-algclosed-extension-module-sections, proof step 2.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem pullback_unit_hom (A : Type*) [Category.{u + 1} A]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [HasWeakSheafify (X.smallGrothendieckTopology (Q := @Etale) @Etale) A]
    [∀ P : Y.Etaleᵒᵖ ⥤ A,
      (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology A) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) A
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app G).hom =
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.lanUnit.app G.obj ≫
      (MorphismProperty.Over.pullback @Etale ⊤ g).op.whiskerLeft
        (toSheafify (D := A) (X.smallGrothendieckTopology (Q := @Etale) @Etale)
          ((MorphismProperty.Over.pullback @Etale ⊤ g).op.leftKanExtension G.obj)) := by
  change (sheafToPresheaf Y.smallEtaleTopology A).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) A
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app G) = _
  dsimp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Functor.lan, ObjectProperty.ι_obj, Functor.id_obj,
    Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    sheafificationAdjunction_unit_app, Functor.whiskeringLeft_obj_map,
    Iso.refl_hom, NatTrans.id_app, Functor.comp_map,
    ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom, Category.assoc]
  erw [Functor.whiskerLeft_id', Category.comp_id, Category.comp_id]

/-- The canonical comparison from the inverse image of the underlying set sheaf to
 the underlying set sheaf of the module inverse image is an isomorphism.
Source: Stacks Project, Tags 03D3 and 03D7 (inverse images), and the concrete
coefficient comparison in lem-sc-algclosed-extension-module-sections, step 2.
(blueprint: lem-sc-etale-module-set-pullback-comparison)

Proof: Base change on the small etale sites preserves finite limits, hence is
representably flat. Its opposite Kan-extension comma categories are filtered and
essentially small. Forgetting modules to sets preserves their filtered colimits,
so the canonical comparison of left Kan extensions is invertible. Forgetting
also preserves limits and filtered colimits, so it commutes with the two plus
constructions computing sheafification; the canonical sheafification comparison
is invertible. Compose these two comparisons. Their unit factorization identities
identify the composite with the adjoint transpose of the forgotten module unit,
which is precisely the displayed map. This works for any ring, including the zero
ring, any morphism of schemes, and the empty schemes. -/
theorem isIso_upperStar_forget_comparison (R : Type (u + 1)) [Ring R]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)).homEquiv
      ((sheafCompose Y.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj G)
      ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj
        ((g)^*[ModuleCat.{u + 1} R].obj G))).symm
        ((sheafCompose Y.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).unit.app G))) := by
  let U := forget (ModuleCat.{u + 1} R)
  let B := MorphismProperty.Over.pullback @Etale ⊤ g
  let L := B.op
  have : X.smallEtaleTopology.PreservesSheafification U := inferInstance
  have h : U.PreservesLeftKanExtensions L := by
    intro F
    have : U.PreservesPointwiseLeftKanExtension F L := by
      intro c
      have : IsFiltered (CostructuredArrow L c) :=
        IsFiltered.of_equivalence (structuredArrowOpEquivalence B c.unop)
      have : PreservesFilteredColimitsOfSize.{u, u + 1} U :=
        preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} U
      exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit U F L c
    exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise U F L
  let e := U.lanCompIsoOfPreserves L
  let e' := sheafComposeNatIso X.smallEtaleTopology U
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)
  let q := (presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map
      ((e.app G.obj).inv) ≫ e'.hom.app (L.lan.obj G.obj)
  have : IsIso q := inferInstance
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
    (Type (u + 1)) (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
    (X.smallGrothendieckTopology (Q := @Etale) @Etale)
  let F := (sheafCompose Y.smallEtaleTopology U).obj G
  let H := (sheafCompose X.smallEtaleTopology U).obj ((g)^*[ModuleCat.{u + 1} R].obj G)
  have hq : (adj.homEquiv F H).symm
      ((sheafCompose Y.smallEtaleTopology U).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).unit.app G)) = q := by
    apply (adj.homEquiv F H).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    apply (sheafToPresheaf _ _).map_injective
    change whiskerRight
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).unit.app G).hom U =
      (adj.unit.app F).hom ≫ B.op.whiskerLeft q.hom
    rw [show (adj.unit.app F).hom = _ from pullback_unit_hom (Type (u + 1)) g F]
    change whiskerRight
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
        (ModuleCat.{u + 1} R) (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
        (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app G).hom U = _
    rw [pullback_unit_hom (ModuleCat.{u + 1} R) g G]
    simp only [whiskerRight_comp, Category.assoc]
    dsimp only [q, ObjectProperty.FullSubcategory.comp_hom]
    rw [← B.op.whiskerLeft_comp]
    have hn := (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).unit.naturality
      ((e.app G.obj).inv)
    have hs := sheafComposeNatTrans_fac X.smallEtaleTopology U
      (sheafificationAdjunction _ _) (sheafificationAdjunction _ _) (L.lan.obj G.obj)
    change (e.app G.obj).inv ≫ toSheafify X.smallEtaleTopology (L.lan.obj G.obj ⋙ U) =
      toSheafify X.smallEtaleTopology (L.lan.obj (G.obj ⋙ U)) ≫
        ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map (e.app G.obj).inv).hom
      at hn
    change whiskerRight (L.leftKanExtensionUnit G.obj) U ≫
      L.whiskerLeft (whiskerRight (toSheafify X.smallEtaleTopology (L.lan.obj G.obj)) U) =
      L.leftKanExtensionUnit (G.obj ⋙ U) ≫ L.whiskerLeft
        (toSheafify X.smallEtaleTopology (L.lan.obj (G.obj ⋙ U)) ≫
          ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map (e.app G.obj).inv).hom ≫
          (e'.hom.app (L.lan.obj G.obj)).hom)
    change toSheafify X.smallEtaleTopology (L.lan.obj G.obj ⋙ U) ≫
      (e'.hom.app (L.lan.obj G.obj)).hom =
      whiskerRight (toSheafify X.smallEtaleTopology (L.lan.obj G.obj)) U at hs
    rw [← Category.assoc (toSheafify X.smallEtaleTopology (L.lan.obj (G.obj ⋙ U))),
      ← hn, Category.assoc, hs]
    rw [B.op.whiskerLeft_comp]
    rw [← Category.assoc]
    change _ = (L.leftKanExtensionUnit (G.obj ⋙ U) ≫
      L.whiskerLeft (U.leftKanExtensionCompIsoOfPreserves G.obj L).inv) ≫ _
    rw [Functor.leftKanExtensionCompIsoOfPreserves_inv_fac]
    rfl
  rw [hq]
  infer_instance

end AlgebraicGeometry.Etale
