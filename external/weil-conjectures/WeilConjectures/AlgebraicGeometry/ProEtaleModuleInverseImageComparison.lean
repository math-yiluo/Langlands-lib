/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying

/-!
# Underlying sheaves and scalar action of pro-etale module inverse image

Source: Stacks Project, Tags 03D2, 03D3 and 04JC.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme

private noncomputable def modelAbelianEquivalence (X : Scheme.{u}) :
    Sheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1} ≌
      Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)
@[irreducible] private noncomputable def modelAbelianAdjunction {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (modelAbelianEquivalence X).functor ⋙
      proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ⋙
      (modelAbelianEquivalence Y).inverse ⊣
    (proEtaleModelBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (proEtaleModelTopology X) (proEtaleModelTopology Y) :=
  (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).restrictFullyFaithful
    (modelAbelianEquivalence X).fullyFaithfulFunctor
    (modelAbelianEquivalence Y).fullyFaithfulFunctor
    (Iso.refl _) (Iso.refl _)
@[irreducible] private noncomputable def modelAbelianPullbackIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) :
    (modelAbelianEquivalence X).inverse ⋙
      Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
        AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (proEtaleModelTopology Y) ⋙
      (modelAbelianEquivalence Y).functor ≅
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} := by
  let a := modelAbelianAdjunction f
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleModelBaseChange f) AddCommGrpCat.{u + 1}
      (proEtaleModelTopology X) (proEtaleModelTopology Y)
  exact Functor.isoWhiskerLeft (modelAbelianEquivalence X).inverse
    (Functor.isoWhiskerRight (b.leftAdjointUniq a) (modelAbelianEquivalence Y).functor)
set_option backward.defeqAttrib.useBackward false in
private noncomputable def toModelForgetIso (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    proEtaleModuleToModel A ⋙
      SheafOfModules.toSheaf
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
          (proEtaleModelTopology X) (ProEt.topology X)).obj A) ≅
    SheafOfModules.toSheaf A ⋙ (modelAbelianEquivalence X).inverse :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N g
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

set_option backward.defeqAttrib.useBackward false in
private noncomputable def fromModelForgetIso (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    proEtaleModuleFromModel A ⋙ SheafOfModules.toSheaf A ≅
    SheafOfModules.toSheaf
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
        (proEtaleModelTopology X) (ProEt.topology X)).obj A) ⋙
      (modelAbelianEquivalence X).functor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N g
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

private theorem underlying {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Nonempty (proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) := by
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  obtain ⟨e⟩ := proEtaleModelModuleInverseImage_underlying f R
  let L := SheafOfModules.pullback (proEtaleModelRingUnit f R)
  let La := Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
    AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (proEtaleModelTopology Y)
  let p := Functor.isoWhiskerLeft (proEtaleModuleToModel A ⋙ L) (fromModelForgetIso Y B)
  let s := Functor.isoWhiskerLeft (proEtaleModuleToModel A)
    (Functor.isoWhiskerRight e (modelAbelianEquivalence Y).functor)
  let t := Functor.isoWhiskerRight (toModelForgetIso X A)
    (La ⋙ (modelAbelianEquivalence Y).functor)
  exact ⟨p ≪≫ s ≪≫ t ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf A) (modelAbelianPullbackIso f)⟩

/-- The module inverse image agrees with ordinary inverse image on underlying abelian
sheaves and on the scalar-action graph, for every morphism of schemes.

Source: Stacks Project, Tags 03D2, 03D3 and 04JC.
(auxiliary; not a blueprint node)

Proof: apply finite-product-preserving set inverse image to the module addition and action.
Functoriality carries the identities expressing the module laws to the same identities in
the inverse-image ring.  Transport the resulting module through the small-model site
 equivalences.  An abelian map from this module is linear precisely when its adjunct is
linear for the ring adjunction unit: naturality of that unit on the scalar-action map and
its product comparison prove both implications.  This gives a module adjunction with the
same right functor as the constructed module pullback.  Uniqueness of left adjoints gives
the natural abelian comparison.  The ring comparison comes from the ring-object lift of
the set adjunction.  For the final assertion, the hypothesis says that the map (a,b,t)
factors through the graph of scalar multiplication.  A finite-limit-preserving functor
preserves this graph and its factorization, giving the displayed sectionwise equality.
No immersion or nonzero coefficient hypothesis is used.
-/
theorem proEtale_moduleInverseImage_comparison
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Nonempty (proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ≅
          SheafOfModules.toSheaf _ ⋙ proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) ∧
    (∃ (eR : (proEtaleSheafInverseImage f (Type (u + 1))).obj
            ((sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).obj R) ≅
            (sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1})).obj
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
          (eM : proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
            (SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙
                proEtaleSheafInverseImage f (Type (u + 1))),
          ∀ (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
            (T : Sheaf (ProEt.topology X) (Type (u + 1)))
            (a : T ⟶ (sheafCompose (ProEt.topology X)
              (CategoryTheory.forget CommRingCat.{u + 1})).obj R)
            (b t : T ⟶ (SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M),
            (∀ (U : X.ProEtᵒᵖ) (x : T.obj.obj U),
              @id (M.val.obj U) (t.hom.app U x) =
                @id (R.obj.obj U) (a.hom.app U x) •
                  @id (M.val.obj U) (b.hom.app U x)) →
            ∀ (V : Y.ProEtᵒᵖ)
              (x : ((proEtaleSheafInverseImage f (Type (u + 1))).obj T).obj.obj V),
              @id (((proEtaleModuleInverseImage f R).obj M).val.obj V)
                ((eM.inv.app M).hom.app V
                  (((proEtaleSheafInverseImage f (Type (u + 1))).map t).hom.app V x)) =
                @id (((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R).obj.obj V)
                  (eR.hom.hom.app V
                    (((proEtaleSheafInverseImage f (Type (u + 1))).map a).hom.app V x)) •
                @id (((proEtaleModuleInverseImage f R).obj M).val.obj V)
                  ((eM.inv.app M).hom.app V
                    (((proEtaleSheafInverseImage f (Type (u + 1))).map b).hom.app V x))) := by
  exact ⟨underlying f R, proEtale_moduleInverseImage_scalarGraph f R⟩

end AlgebraicGeometry.Scheme
