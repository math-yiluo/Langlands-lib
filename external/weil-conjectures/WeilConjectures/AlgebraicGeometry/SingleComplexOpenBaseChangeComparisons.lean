/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # Explicit open base-change comparisons

Source: Stacks Project, Tags 08FE, 08HY and 0DJ9.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- The explicit additivity witnesses require a larger typeclass-search budget.
/-- The sectionwise open direct-image comparison, derived using exact restriction
and preservation of K-injectives. This constructs the isomorphism rather than
selecting an arbitrary witness of its existence.
Source: Stacks Project, Tags 08FE and 08BS.
(blueprint: def-pc-n3-open-base-change-comparisons). -/
noncomputable def singleComplexOpenDirectImageIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    schemeDerivedDirectImage f ⋙ (schemeOpenRestriction Y V).mapDerivedCategory ≅
      (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory ⋙
        schemeDerivedDirectImage (f ∣_ V) := by
  classical
  let rX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (f ⁻¹ᵁ V)
  let eX := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (f ⁻¹ᵁ V)))
    (D := SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv (f ⁻¹ᵁ V))
  let rY := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V
  let eY := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
    (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv V)
  have : rX.Additive := Functor.additive_of_preserves_binary_products _
  have : eX.Additive := Functor.additive_of_preserves_binary_products _
  have : (rX ⋙ eX).Additive := Functor.additive_of_preserves_binary_products _
  have : (rY ⋙ eY).Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits (rX ⋙ eX) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (rX ⋙ eX) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (rY ⋙ eY) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (rY ⋙ eY) := comp_preservesFiniteColimits _ _
  have : rX.PreservesKInjectiveComplexes :=
    ⟨fun I _ ↦ kInjective_of_restrict_open X.toRingedSpace (f ⁻¹ᵁ V) I⟩
  have : eX.PreservesKInjectiveComplexes := inferInstance
  have : (rX ⋙ eX).PreservesKInjectiveComplexes := inferInstance
  -- The underived comparison is the sectionwise identity from Tag 08FE.
  have e : RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙ (rY ⋙ eY) ≅
      (rX ⋙ eX) ⋙ RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom := by
    refine Functor.isoWhiskerLeft _ (Scheme.Modules.overFunctorEquiv V) ≪≫
      ?_ ≪≫ Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ V)).symm _
    change Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙ Scheme.Modules.pushforward (f ∣_ V)
    refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
    refine SheafOfModules.pushforwardCongr₂ _ ?_ ?_
    · refine NatIso.ofComponents (fun W ↦ eqToIso ?_) ?_
      · exact image_morphismRestrict_preimage f V W
      · cat_disch
    · ext W x
      simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
      dsimp
      exact congr($(morphismRestrict_app f V W.unop) x).symm
  -- Derive the comparison, using exactness on Y and K-injectivity preservation on X.
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{w, w, w}
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) (rY ⋙ eY)).symm ≪≫
    Functor.rightDerivedFunctorNatIso.{u, u, u + 1, u + 1, w, w} e ≪≫
    Functor.rightDerivedFunctorCompIso.{u, u, u, u + 1, u + 1, u + 1,
      w, w, w} (rX ⋙ eX)
      (RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom) ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory.{w, w} (rX ⋙ eX))
      (schemeDerivedDirectImage (f ∣_ V))

/-- Source comparison for the bare open base-change identity. Its factors are
open pullback, pullback composition along the restricted square, open pullback
on the base, and the explicit direct-image comparison.
Source: Stacks Project, Tags 08FE, 0D5S and 0DJ9, first paragraph.
(blueprint: def-pc-n3-open-base-change-comparisons). -/
noncomputable def singleComplexOpenBaseChangeSourceIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (K : schemeDerivedCategory X)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V) :
    (schemeOpenRestriction S' V').mapDerivedCategory.obj
        ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj K)) ≅
      (derivedPullback (g.resLE V V' hV')).obj
        ((schemeDerivedDirectImage (f ∣_ V)).obj
          ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K)) := by
  classical
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  let M := (schemeDerivedDirectImage f).obj K
  exact (singleComplexOpenPullbackIso S' V').symm.app ((derivedPullback g).obj M) ≪≫
    (c V'.ι g).app M ≪≫
    eqToIso (congrArg (fun k ↦ (derivedPullback k).obj M)
      (Scheme.Hom.resLE_comp_ι g hV').symm) ≪≫
    (c (g.resLE V V' hV') V.ι).symm.app M ≪≫
    (derivedPullback (g.resLE V V' hV')).mapIso
      ((singleComplexOpenPullbackIso S V).app M) ≪≫
    (derivedPullback (g.resLE V V' hV')).mapIso
      ((singleComplexOpenDirectImageIso f V).app K)

end AlgebraicGeometry
