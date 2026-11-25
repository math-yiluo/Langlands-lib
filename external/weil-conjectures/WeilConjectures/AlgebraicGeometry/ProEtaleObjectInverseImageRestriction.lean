/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Inverse image along an object of the small pro-etale site

Source: Stacks Project, Sites and Sheaves, Tags 03CE, 00VC, 00XZ, 00WH and 0H7J;
Modules on Sites, Tags 03D2 and 03EK; pro-etale functoriality, Tag 09A5
(auxiliary; not a blueprint node).

The comparison data below spell out the canonical presheaf coprojections and
sheafification unit. The theorem applies to an arbitrary site object, with no
monomorphism or finiteness hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The distinguished pair `(U → X, (id, str))` in the inverse-image index.
The chosen pullback puts the variable factor first. Its arrow is the unit of
composition left adjoint to base change, hence is exactly the pair of the identity
and the structure map, rather than an arbitrary arrow to the fibre product.
Source: Stacks, Tags 03CE and 00VC
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleObjectInverseImageIndexPoint {X : Scheme.{u}} (W : X.ProEt)
    (U : W.left.ProEt) : proEtaleInverseImageIndex W.hom U :=
  StructuredArrow.mk
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).unit.app U)

/-- Clause (1)'s canonical comparison data for a specified category of values.
`presheafIso` is restriction to the object followed by the presheaf inverse image;
its components are the distinguished coprojections, expressed using the Kan unit.
The final equation identifies the inverse of `sheafIso` with those coprojections
followed by the actual sheafification unit. Both isomorphisms are natural in the
sheaf, and their components are presheaf/sheaf morphisms, hence natural in site objects.
This structure only packages the assertions; it does not choose any comparison.
Source: Stacks, Tags 03CE, 00VC and 00WH
(auxiliary; not a blueprint node). -/
structure ProEtaleObjectRestrictionComparison {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology W.left) D] where
  presheafIso :
    AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ⋙
        sheafToPresheaf (ProEt.topology W.left) D ≅
      sheafToPresheaf (ProEt.topology X) D ⋙ (proEtaleBaseChange W.hom).op.lan
  coprojection : ∀ (G : Sheaf (ProEt.topology X) D) (U : W.left.ProEt),
    (presheafIso.hom.app G).app (op U) =
      ((proEtaleBaseChange W.hom).op.leftKanExtensionUnit G.obj).app
          (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) ≫
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj).map
          (proEtaleObjectInverseImageIndexPoint W U).hom.op
  sheafification_isIso : ∀ G : Sheaf (ProEt.topology X) D,
    IsIso (toSheafify (ProEt.topology W.left)
      (((proEtaleBaseChange W.hom).op.lan).obj G.obj))
  sheafIso : proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D ≅
    AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop
  sheafIso_inv : ∀ G : Sheaf (ProEt.topology X) D,
    (sheafIso.inv.app G).hom = presheafIso.hom.app G ≫
      toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)

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

end AlgebraicGeometry.Scheme
