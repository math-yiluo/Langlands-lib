/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.CategoryTheory.Derived.DerivedExactMateSupplement
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero

/-! # Sheaf and derived-unit normalizations of the Cartesian sum mate

Source: Stacks Project, Tags 0F4L, 0F7B and 0F7F; the factorization equations
for derived adjunctions. No compactification or properness is used here.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private lemma homotopy_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (N : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app N = 𝟙 _ := by
  obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective N
  change (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

private lemma two_iso_cancel
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (e : X ≅ Y) {Z T : D} (i : Z ≅ F.obj Y) (f : Z ⟶ T) :
    i.hom ≫ F.map e.inv ≫ F.map e.hom ≫ i.inv ≫ f = f := by
  rw [← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp,
    Iso.hom_inv_id_assoc]

private lemma conjugate_comparison_inv
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    conjugateEquiv a b ((a.ofNatIsoRight e).leftAdjointUniq b).inv = e.hom := by
  apply conjugateEquiv_eq_of_unit
  intro M
  have h := Adjunction.unit_leftAdjointUniq_hom_app b (a.ofNatIsoRight e) M
  rw [← Adjunction.leftAdjointUniq_inv_app] at h
  exact h.symm

private lemma derived_square_mate_units
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    [G.Additive] [G'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (d : L ⊣ R) (d' : L' ⊣ R') (β : G ⋙ L' ≅ L ⋙ G') :
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit R G ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (mateEquiv d.mapDerivedCategoryRightDerivedAdjunction
            d'.mapDerivedCategoryRightDerivedAdjunction
            (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso β).hom)) =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
          (mateEquiv d d' (TwoSquare.mk _ _ _ _ β.hom)) (.up ℤ))
          DerivedCategory.Qh ≫
        Functor.mapDerivedCategoryCompRightDerivedFunctorUnit G' R' := by
  let σ := TwoSquare.mk _ _ _ _ β.hom
  have hn (N : HomotopyCategory C₂ (.up ℤ)) :
      (Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj N) ≫
          G'.mapDerivedCategory.map
            (L.mapDerivedCategoryFactorsh.hom.app N) ≫
          G'.mapDerivedCategoryFactorsh.hom.app
            ((L.mapHomotopyCategory (.up ℤ)).obj N) =
        L'.mapDerivedCategory.map
            (G.mapDerivedCategoryFactorsh.hom.app N) ≫
          L'.mapDerivedCategoryFactorsh.hom.app
            ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app N) := by
    have h := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj β N
    simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
      homotopy_comp_inv, Category.id_comp, Category.comp_id] at h
    apply (cancel_epi
      (L'.mapDerivedCategoryFactorsh.inv.app
        ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
        L'.mapDerivedCategory.map
          (G.mapDerivedCategoryFactorsh.inv.app N))).1
    have hc := two_iso_cancel L'.mapDerivedCategory
      (G.mapDerivedCategoryFactorsh.app N)
      (L'.mapDerivedCategoryFactorsh.app
        ((G.mapHomotopyCategory (.up ℤ)).obj N)).symm
      (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app N))
    simpa only [Category.assoc, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv]
      using h.trans hc.symm
  ext N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app']
  rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  have hm := Adjunction.derivedExact_mateEquiv_app_fac d d' σ
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso β).hom) hn N
  rw [homotopy_comp_inv, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Category.assoc, hm]
  exact Iso.inv_hom_id_app_assoc G.mapDerivedCategoryFactorsh
    ((R.mapHomotopyCategory (.up ℤ)).obj N) _

/-- Right derivation computes the mate of inverse sum exchange from its sheaf mate.
Source: Stacks Project, Tag 0F7F; the derived-adjunction factorization equations
(blueprint: lem-pur-cartesian-sum-mate-units).

Proof: conjugate the sheaf base-change isomorphism through the composite
adjunctions. The leftAdjointUniq unit equation and iterated-mates identity identify
its inverse with inverse sum exchange. Exact localization preserves that inverse
mate. The factorization theorem for exact derived squares then computes its
forward mate using the ordinary sheaf mate and the two right-derived units.
Cancel only the exact-functor localization isomorphisms. This needs no properness,
Noetherianity, compactification, boundedness or finiteness of coefficients. -/
theorem cartesian_sum_mate_units
    (A : Type (u + 1)) [CommRing A]
    {W Y' Z Y : Scheme.{u}}
    (q : W ⟶ Y') (p : Z ⟶ Y)
    (b : W ⟶ Z) [Etale b]
    (v : Y' ⟶ Y) [Etale v]
    (sq : IsPullback b q p v)
    [IsIso (((mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance)).symm
      (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        sq.toCommSq).hom)))] :
    let θ := (mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (TwoSquare.mk _ _ _ _ (etaleLowerShriekBaseChangeIso A sq).hom))
    let sumEx := ((mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance)).symm
      (TwoSquare.mk _ _ _ _
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).hom))
    let gam := (mateEquiv
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (TwoSquare.mk _ _ _ _ (inv sumEx)))
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit
      (lowerStar (ModuleCat.{u + 1} A) q)
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance)) ≫
      Functor.whiskerLeft DerivedCategory.Qh gam =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory θ (.up ℤ)) DerivedCategory.Qh ≫
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
        (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance)
        (lowerStar (ModuleCat.{u + 1} A) p) := by
  dsimp only
  let B := ModuleCat.{u + 1} A
  let a := etaleLowerShriekUpperStarAdjunction B v inferInstance
  let a' := etaleLowerShriekUpperStarAdjunction B b inferInstance
  let d := upperStarLowerStarAdjunction B q
  let d' := upperStarLowerStarAdjunction B p
  let χ := squareUpperStarIso B sq.toCommSq
  let β := etaleLowerShriekBaseChangeIso A sq
  let sd := ((mateEquiv
    (derivedEtaleLowerShriekUpperStarAdjunction B v inferInstance)
    (derivedEtaleLowerShriekUpperStarAdjunction B b inferInstance)).symm
      (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq.toCommSq).hom))
  have (F : Sheaf Z.smallEtaleTopology B) :
      IsIso ((baseChangeMap B sq.toCommSq).app F) :=
    isIso_baseChangeMap_app_of_flat A sq F
  have : IsIso (baseChangeMap B sq.toCommSq) := NatIso.isIso_of_isIso_app _
  have hs : ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ χ.hom)) = β.inv := by
    apply (conjugateEquiv (a.comp d') (d.comp a')).injective
    rw [← iterated_mateEquiv_conjugateEquiv a a' d d', Equiv.apply_symm_apply]
    change baseChangeMap B sq.toCommSq = _
    exact (conjugate_comparison_inv (a.comp d') (d.comp a')
      (asIso (baseChangeMap B sq.toCommSq))).symm
  have : IsIso ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ χ.hom)) := by
    rw [hs]
    infer_instance
  have hl := (exact_localization_inverse_mate a a' χ).2.1
  have hi : asIso ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ χ.hom)) =
      β.symm := Iso.ext hs
  rw [hi] at hl
  have hd : inv sd = (Functor.mapDerivedCategorySquareIso β).hom := by
    have he : sd = (Functor.mapDerivedCategorySquareIso β).inv := by
      change _ = _ at hl
      simpa only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
        exactDerivedSquareUpperStarIso, sd, χ, a, a', Category.assoc,
        derivedEtaleLowerShriekUpperStarAdjunction, exactLocalizationDerivedAdjunction] using hl
    apply (cancel_epi sd).1
    rw [IsIso.hom_inv_id, he, Iso.inv_hom_id]
  change Functor.rightDerivedFunctorCompMapDerivedCategoryUnit
      (lowerStar B q) (etaleLowerShriek B v inferInstance) ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (mateEquiv (mapDerivedUpperStarLowerStarAdjunction B q)
          (mapDerivedUpperStarLowerStarAdjunction B p)
          (TwoSquare.mk _ _ _ _ (inv sd))) = _
  rw [hd]
  exact derived_square_mate_units d d' β

end AlgebraicGeometry.Etale
