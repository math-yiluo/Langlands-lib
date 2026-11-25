/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction

/-!
# Inverse image along an object of the small pro-etale site

The comparison data below spell out the canonical presheaf coprojections and
sheafification unit. The theorem applies to an arbitrary site object, with no
monomorphism or finiteness hypothesis.

## References

* Stacks Project, Sites and Sheaves, Tags 03CE, 00VC, 00XZ, 00WH and 0H7J
* Modules on Sites, Tags 03D2 and 03EK
* Stacks Project, Tag 09A5
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def restrictionPresheafIso {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D] :
    AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ⋙
        sheafToPresheaf (ProEt.topology W.left) D ≅
      sheafToPresheaf (ProEt.topology X) D ⋙ (proEtaleBaseChange W.hom).op.lan := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom
    W.prop trivial).op.whiskerLeft D
  let b := (proEtaleBaseChange W.hom).op.lanAdjunction D
  exact Functor.isoWhiskerLeft (sheafToPresheaf (ProEt.topology X) D)
    (a.leftAdjointUniq b)

private theorem restrictionPresheafIso_coprojection {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    (G : Sheaf (ProEt.topology X) D) (U : W.left.ProEt) :
    ((restrictionPresheafIso W D).hom.app G).app (op U) =
      ((proEtaleBaseChange W.hom).op.leftKanExtensionUnit G.obj).app
          (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) ≫
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj).map
          (proEtaleObjectInverseImageIndexPoint W U).hom.op := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
    W.hom W.prop trivial).op.whiskerLeft D
  let b := (proEtaleBaseChange W.hom).op.lanAdjunction D
  have h : (a.leftAdjointUniq b).hom.app G.obj =
      (a.homEquiv _ _).symm (b.unit.app G.obj) := by
    apply (a.homEquiv _ _).injective
    exact (Adjunction.homEquiv_leftAdjointUniq_hom_app a b G.obj).trans
      (Equiv.apply_symm_apply _ _).symm
  change ((a.leftAdjointUniq b).hom.app G.obj).app (op U) = _
  rw [h, Adjunction.homEquiv_counit]
  simp only [a, b, NatTrans.comp_app, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app, Adjunction.whiskerLeft_counit_app_app,
    Functor.lanAdjunction_unit]
  rfl

private theorem restrictionLan_isSheaf {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    (G : Sheaf (ProEt.topology X) D) :
    Presheaf.IsSheaf (ProEt.topology W.left)
      (((proEtaleBaseChange W.hom).op.lan).obj G.obj) :=
  (Presheaf.isSheaf_of_iso_iff ((restrictionPresheafIso W D).app G)).mp
    ((AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop).obj G).property

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def restrictionComparison {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology W.left) D] :
    ProEtaleObjectRestrictionComparison W D := by
  let p := restrictionPresheafIso W D
  have hq (G : Sheaf (ProEt.topology X) D) :
      IsIso (toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)) :=
    isIso_toSheafify _ (restrictionLan_isSheaf W D G)
  let e : AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ≅
      proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D :=
    NatIso.ofComponents (fun G ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (p.app G ≪≫ asIso (toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)))) (by
      intro G H f
      apply Sheaf.hom_ext
      change _ ≫ (p.hom.app H ≫ toSheafify _ _) =
        (p.hom.app G ≫ toSheafify _ _) ≫ _
      have hp := p.hom.naturality f
      change ((AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop).map
        f).hom ≫ p.hom.app H = p.hom.app G ≫
          ((proEtaleBaseChange W.hom).op.lan).map f.hom at hp
      rw [← Category.assoc, hp, Category.assoc]
      have hfmap :
          ((proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D).map f).hom =
          sheafifyMap (ProEt.topology W.left)
            (((proEtaleBaseChange W.hom).op.lan).map f.hom) := by
        rfl
      rw [hfmap]
      rw [Category.assoc]
      congr 1
      exact toSheafify_naturality (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).map f.hom))
  exact
    { presheafIso := p
      coprojection := restrictionPresheafIso_coprojection W D
      sheafification_isIso := hq
      sheafIso := e.symm
      sheafIso_inv := fun _ ↦ rfl }

private noncomputable def restrictionConstantIso {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A] :
    proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A) := by
  let F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop
  have : F.IsContinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap W.prop
  have : F.IsCocontinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap W.prop
  exact (F.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology W.left) (ProEt.topology X)).app
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))

private theorem restrictionConstantIso_unit {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A] (U : W.left.ProEt) :
    (toSheafify (ProEt.topology W.left)
      ((Functor.const W.left.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫
      (restrictionConstantIso W A).hom.hom.app (op U) =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) := by
  let F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop
  have : F.IsContinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap W.prop
  have : F.IsCocontinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap W.prop
  exact congrArg (fun f ↦ f.app (op U))
    (F.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
      (ProEt.topology W.left) (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))

private theorem inverseImageAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    ((proEtaleSheafAdjunction (X := X) (Y := Y) f CommRingCat.{u + 1}).unit.app R).hom =
      (proEtaleBaseChange f).op.lanUnit.app R.obj ≫
        (proEtaleBaseChange f).op.whiskerLeft
          (toSheafify (ProEt.topology X) ((proEtaleBaseChange f).op.lan.obj R.obj)) := by
  change (sheafToPresheaf _ _).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _).unit.app R) = _
  rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp

private theorem coefficientDirect_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (U : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app U ≫
      (proEtaleCoefficientDirectImageMap f A).hom.app U =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
        ((proEtaleBaseChange f).op.obj U) := by
  have h := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (proEtaleConstantRing X A))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))))
  exact congrArg (fun z ↦ z.app U) h
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_restriction_counit {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
    Functor.whiskerRight (NatTrans.op
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).counit)
        (proEtaleConstantRing X A).obj =
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
        (proEtaleBaseChange W.hom).op.whiskerLeft e.hom.hom := by
  let T := (proEtaleSheafDirectImage W.hom CommRingCat.{u + 1}).obj
    ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      W.hom W.prop).obj (proEtaleConstantRing X A))
  apply sheafify_hom_ext (ProEt.topology X) _ _ T.property
  apply NatTrans.ext
  funext U
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, coefficientDirect_unit]
  erw [he]
  have h := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
        W.hom W.prop trivial).counit.app U.unop).op
  simpa [proEtaleConstantRing, constantSheaf, proEtaleBaseChange] using h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_restriction_unit {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
    e.hom.hom ≫ (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).op.whiskerLeft
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
      Functor.whiskerRight (NatTrans.op
        (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).unit)
          (proEtaleConstantRing W.left A).obj = 𝟙 _ := by
  apply sheafify_hom_ext (ProEt.topology W.left) _ _ (proEtaleConstantRing W.left A).property
  apply NatTrans.ext
  funext U
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app]
  rw [← Category.assoc, ← Category.assoc, he]
  erw [coefficientDirect_unit]
  have h := (toSheafify (ProEt.topology W.left)
    ((Functor.const W.left.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
        W.hom W.prop trivial).unit.app U.unop).op
  simpa [proEtaleConstantRing, constantSheaf, proEtaleBaseChange] using h.symm

end AlgebraicGeometry.Scheme
