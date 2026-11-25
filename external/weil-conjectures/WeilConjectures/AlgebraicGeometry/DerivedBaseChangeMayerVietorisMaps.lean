/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps

/-! # Concrete maps for relative Mayer--Vietoris base change

Source: Stacks Project, Tags 08BV, 08HY and 0DJ9
(blueprint: def-pc-rf-mv-base-change-components).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The derived pullback adjunction pinned to the same counits as the base-change map.
Source: Stacks Project, Tags 079W and 08HY
(blueprint: def-pc-rf-mv-base-change-components). -/
abbrev mvDerivedPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ⊣ schemeDerivedDirectImage f :=
  canonicalPullbackAdjunction f

/-- The derived adjunction of exact open restriction, constructed from its underived
adjunction. Source: Stacks Project, Tag 08BV
(blueprint: def-pc-rf-mv-base-change-components). -/
@[irreducible] def mvOpenRestrictionAdjunction (X : Scheme.{u}) (U : X.Opens) :
    (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι :=
  let a : schemeOpenRestriction X U ⊣
      RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom :=
    (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv U).symm
  a.mapDerivedCategoryRightDerivedAdjunction

/-- The comparison between pullback by an open immersion and exact restriction is
constructed by uniqueness of left adjoints; its unit and counit identities are those
of `Adjunction.leftAdjointUniq`. Source: Stacks Project, Tags 08DW and 079W
(blueprint: def-pc-rf-mv-base-change-components). -/
@[irreducible] def mvOpenPullbackIso (X : Scheme.{u}) (U : X.Opens) :
    derivedPullback U.ι ≅ (schemeOpenRestriction X U).mapDerivedCategory :=
  (mvDerivedPullbackAdjunction U.ι).leftAdjointUniq (mvOpenRestrictionAdjunction X U)

/-- The open comparison respects the adjunction unit by construction.
Source: Stacks Project, Tag 079W; Mathlib `Adjunction.unit_leftAdjointUniq_hom_app`
(blueprint: def-pc-rf-mv-base-change-components). -/
private theorem mvOpenPullbackIso_unit (X : Scheme.{u}) (U : X.Opens)
    (K : schemeDerivedCategory X) :
    (mvDerivedPullbackAdjunction U.ι).unit.app K ≫
        (schemeDerivedDirectImage U.ι).map ((mvOpenPullbackIso X U).hom.app K) =
      (mvOpenRestrictionAdjunction X U).unit.app K := by
  unfold mvOpenPullbackIso
  exact Adjunction.unit_leftAdjointUniq_hom_app
    (mvDerivedPullbackAdjunction U.ι) (mvOpenRestrictionAdjunction X U) K

/-- The same comparison respects the adjunction counit.
Source: Stacks Project, Tag 079W; Mathlib `Adjunction.leftAdjointUniq_hom_app_counit`
(blueprint: def-pc-rf-mv-base-change-components). -/
private theorem mvOpenPullbackIso_counit (X : Scheme.{u}) (U : X.Opens)
    (K : schemeDerivedCategory U.toScheme) :
    (mvOpenPullbackIso X U).hom.app ((schemeDerivedDirectImage U.ι).obj K) ≫
        (mvOpenRestrictionAdjunction X U).counit.app K =
      (mvDerivedPullbackAdjunction U.ι).counit.app K := by
  unfold mvOpenPullbackIso
  exact Adjunction.leftAdjointUniq_hom_app_counit
    (mvDerivedPullbackAdjunction U.ι) (mvOpenRestrictionAdjunction X U) K

/-- Canonical pullback/restriction comparison. Unlike a witness of bare `Nonempty`,
this is constructed from the pinned pullback composition comparisons and the open
adjunctions. Source: Stacks Project, Tags 0D5S and 08DW
(blueprint: def-pc-rf-mv-base-change-components). -/
@[irreducible] def mvPullbackOpenRestrictionIso {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    derivedPullback f ⋙ (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory ≅
      (schemeOpenRestriction Y V).mapDerivedCategory ⋙
        derivedPullback (f.resLE V (f ⁻¹ᵁ V) le_rfl) :=
  let c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
    fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) a b
  Functor.isoWhiskerLeft (derivedPullback f) (mvOpenPullbackIso X (f ⁻¹ᵁ V)).symm ≪≫
    c (f ⁻¹ᵁ V).ι f ≪≫
    eqToIso (congrArg (fun k : (f ⁻¹ᵁ V).toScheme ⟶ Y => derivedPullback k)
      (Scheme.Hom.resLE_comp_ι f (U := V) le_rfl).symm) ≪≫
    (c (f.resLE V (f ⁻¹ᵁ V) le_rfl) V.ι).symm ≪≫
    Functor.isoWhiskerRight (mvOpenPullbackIso Y V)
      (derivedPullback (f.resLE V (f ⁻¹ᵁ V) le_rfl))

/-- The explicit first two maps and boundary of an open-cover triangle.
The overlap is a separate open, so inverse-image covers do not require casts.
Source: Stacks Project, Tag 08BV
(blueprint: def-pc-rf-mv-base-change-components). -/
def mvBaseChangeTriangle (X : Scheme.{u}) (U V W : X.Opens)
    (iU : W ⟶ U) (iV : W ⟶ V)
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjW : (schemeOpenRestriction X W).mapDerivedCategory ⊣ schemeDerivedDirectImage W.ι)
    (K : schemeDerivedCategory X)
    (δ : (schemeDerivedDirectImage W.ι).obj
      ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ⟶ K⟦(1 : ℤ)⟧) :
    Triangle (schemeDerivedCategory X) :=
  Triangle.mk (biprod.lift (adjU.unit.app K) (adjV.unit.app K))
    (biprod.desc (schemeDerivedOpenDirectImageRestriction X iU adjU adjW K)
      (-(schemeDerivedOpenDirectImageRestriction X iV adjV adjW K))) δ

/-- The pasted base-change component on an open. This is an explicit map, with
no witness chosen from an existence statement. Source: Stacks, Tags 08HY and 0DJ9
(blueprint: def-pc-rf-mv-base-change-components). -/
def mvBaseChangeOpenMap {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback g').obj K ⟶ K') (W : X.Opens) :
    (schemeDerivedDirectImage f ⋙ derivedPullback g).obj
        ((schemeDerivedDirectImage W.ι).obj
          ((schemeOpenRestriction X W).mapDerivedCategory.obj K)) ⟶
      (schemeDerivedDirectImage f').obj
        ((schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).obj
          ((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.obj K')) :=
  schemeDerivedBaseChangeMap f f' g g' h
      ((schemeDerivedDirectImage W.ι).obj
        ((schemeOpenRestriction X W).mapDerivedCategory.obj K)) ≫
    (schemeDerivedDirectImage f').map (
      schemeDerivedBaseChangeMap W.ι (g' ⁻¹ᵁ W).ι g'
          (g'.resLE W (g' ⁻¹ᵁ W) le_rfl) (Scheme.Hom.resLE_comp_ι g' le_rfl)
          ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ≫
        (schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).map (
          (mvPullbackOpenRestrictionIso g' W).inv.app K ≫
          (schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.map ψ))

/-- The middle component is the sum of its two diagonal components, written using
images of the biproduct inclusions and projections. Source: Stacks, Tag 0DJ9
(blueprint: def-pc-rf-mv-base-change-components). -/
def mvBaseChangeMiddle {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback g').obj K ⟶ K') (U V : X.Opens) :
    (schemeDerivedDirectImage f ⋙ derivedPullback g).obj
        (((schemeDerivedDirectImage U.ι).obj
            ((schemeOpenRestriction X U).mapDerivedCategory.obj K)) ⊞
          ((schemeDerivedDirectImage V.ι).obj
            ((schemeOpenRestriction X V).mapDerivedCategory.obj K))) ⟶
      (schemeDerivedDirectImage f').obj
        (((schemeDerivedDirectImage (g' ⁻¹ᵁ U).ι).obj
            ((schemeOpenRestriction X' (g' ⁻¹ᵁ U)).mapDerivedCategory.obj K')) ⊞
          ((schemeDerivedDirectImage (g' ⁻¹ᵁ V).ι).obj
            ((schemeOpenRestriction X' (g' ⁻¹ᵁ V)).mapDerivedCategory.obj K'))) :=
  (schemeDerivedDirectImage f ⋙ derivedPullback g).map biprod.fst ≫
      mvBaseChangeOpenMap f f' g g' h K K' ψ U ≫
        (schemeDerivedDirectImage f').map biprod.inl +
    (schemeDerivedDirectImage f ⋙ derivedPullback g).map biprod.snd ≫
      mvBaseChangeOpenMap f f' g g' h K K' ψ V ≫
        (schemeDerivedDirectImage f').map biprod.inr

end AlgebraicGeometry
