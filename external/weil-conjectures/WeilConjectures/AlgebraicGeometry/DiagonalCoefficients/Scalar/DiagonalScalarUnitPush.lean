/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush

/-! # Scalar transport of the coefficient-unit arrow

Source: diagonal tower coefficient changes (1), mate and unit normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint derivedScalars RestrictionSquare.mate

private theorem mate_transpose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {E : C ⥤ D} {Res : D ⥤ C} {E' : C' ⥤ D'} {Res' : D' ⥤ C'}
    (ad : E ⊣ Res) (ad' : E' ⊣ Res')
    (R : C ⥤ C') (R' : D ⥤ D') (e : R' ⋙ Res' ≅ Res ⋙ R)
    {U : C'} {V : C} {W : D} (c : U ⟶ R.obj V) (v : E.obj V ⟶ W) :
    ad'.homEquiv _ _
        (E'.map c ≫ (Adjunction.pushHomOfComapIso ad ad' e).app V ≫ R'.map v) =
      c ≫ R.map (ad.homEquiv _ _ v) ≫ e.inv.app W := by
  have hm := unit_mateEquiv_symm ad ad'
    (TwoSquare.mk Res R' R Res' e.inv) V
  change R.map (ad.unit.app V) ≫ e.inv.app (E.obj V) =
    ad'.unit.app (R.obj V) ≫
      Res'.map ((Adjunction.pushHomOfComapIso ad ad' e).app V) at hm
  have hn := e.inv.naturality v
  change R.map (Res.map v) ≫ e.inv.app W =
    e.inv.app (E.obj V) ≫ Res'.map (R'.map v) at hn
  rw [Adjunction.homEquiv_unit, Res'.map_comp, Res'.map_comp]
  rw [← reassoc_of% (ad'.unit.naturality c), ← reassoc_of% hm]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [hn]

-- Elaborating the dependent coefficient categories and both endpoint adjunctions.
/-- The scalar/direct-image mate carries the canonical coefficient-unit arrow to itself.
Source: diagonal tower coefficient changes (1), scalar adjunction of coefficient one.
(blueprint: lem-diagonal-scalar-unit-push).

Proof: transpose the equation under extension/restriction on Y. The mate identity
turns its left side into the restriction-square comparison after the extension unit
on P. Endpoint.normalization replaces the two transposed endpoint isomorphisms by
the specified semilinear coefficient maps. On ordinary modules the resulting square
commutes because the structural ring map sends one to one. Evaluate the full
restriction-square derived-unit normalization on the single regular module and
cancel the exact single-complex comparisons. This is the transposed equality, hence
the required equality by injectivity of the adjunction bijection. Exactness of
extension is never used, so the same calculation applies to a nonflat quotient and
the zero ring. There is no local Chern arrow, line endpoint, completed coefficient
or finite realization in this equation. -/
theorem scalar_unit_push
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (Y : Scheme.{u})
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ (ProjectiveLine Y ↘ Y)))
    (R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' (ProjectiveLine Y ↘ Y)))
    (s : RestrictionSquare a (ProjectiveLine Y ↘ Y) R R')
    (uY : Endpoint a (Mod.regular (condensedRingObj Λ Y))
      (Mod.regular (condensedRingObj Λ' Y)) (coefficientMap a Y))
    (uP : Endpoint a (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y))) :
    (derivedScalars a Y).map (coefficientUnitPush Λ Y R) ≫
        (s.mate a).app (unit Λ (ProjectiveLine Y)) ≫ R'.R.map uP.iso.hom =
      uY.iso.hom ≫ coefficientUnitPush Λ' Y R' := by
  let f := ProjectiveLine Y ↘ Y
  let U := Mod.regular (condensedRingObj Λ (ProjectiveLine Y))
  let U' := Mod.regular (condensedRingObj Λ' (ProjectiveLine Y))
  let m := coefficientOrdinaryUnit Λ Y
  let m' := coefficientOrdinaryUnit Λ' Y
  have hm : m ≫ (CondensedRing.lowerStar Λ f).map uP.semilinear.hom =
      uY.semilinear.hom ≫ (Mod.comap (coefficientMap a Y)).map m' ≫
        (CondensedRing.comapLowerStarIso a f).hom.app U' := by
    have hm₀ : m.hom = condensedPushforwardHom Λ f :=
      coefficientOrdinaryUnit_underlying Λ Y
    have hm₁ : m'.hom = condensedPushforwardHom Λ' f :=
      coefficientOrdinaryUnit_underlying Λ' Y
    apply Mod.Hom.ext
    change m.hom ≫ (lowerStar Ab.{u + 1} f).map uP.semilinear.hom.hom =
      uY.semilinear.hom.hom ≫ m'.hom ≫
        ((CondensedRing.comapLowerStarIso a f).hom.app U').hom
    rw [hm₀, hm₁, uP.semilinear.underlying, uY.semilinear.underlying]
    rw [CondensedRing.comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom]
    exact (condensedPushforwardHom_comp_map_coefficientMap a f).trans
      (congrArg (fun h => coefficientMap a Y ≫ h) (Category.comp_id _)).symm
  have hs := singlePushComparison_square
    (Mod.comap (coefficientMap a (ProjectiveLine Y)))
    (Mod.comap (coefficientMap a Y)) R' R
    (CondensedRing.comapLowerStarIso a f) s U'
  let adY : derivedScalars a Y ⊣
      (Mod.comap (coefficientMap a Y)).mapDerivedCategory := by
    unfold derivedScalars
    exact Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)
  let adP : derivedScalars a (ProjectiveLine Y) ⊣
      (Mod.comap (coefficientMap a (ProjectiveLine Y))).mapDerivedCategory := by
    unfold derivedScalars
    exact Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a (ProjectiveLine Y))
  have hP : adP.homEquiv _ _ uP.iso.hom =
      (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
          uP.semilinear.hom ≫
        ((Mod.comap (coefficientMap a (ProjectiveLine Y))).mapDerivedCategorySingleFunctor
          0).inv.app U' := by
    with_unfolding_all exact uP.normalization
  have hY : adY.homEquiv _ _ uY.iso.hom =
      (DerivedCategory.singleFunctor (Modules Λ Y) 0).map uY.semilinear.hom ≫
        ((Mod.comap (coefficientMap a Y)).mapDerivedCategorySingleFunctor 0).inv.app
          (Mod.regular (condensedRingObj Λ' Y)) := by
    with_unfolding_all exact uY.normalization
  apply (adY.homEquiv (unit Λ Y) _).injective
  unfold RestrictionSquare.mate
  with_unfolding_all
    change adY.homEquiv _ _
      ((derivedScalars a Y).map (coefficientUnitPush Λ Y R) ≫
        (Adjunction.pushHomOfComapIso adP adY s.iso).app _ ≫ R'.R.map uP.iso.hom) = _
  rw [mate_transpose]
  rw [hP, adY.homEquiv_naturality_right, hY]
  unfold coefficientUnitPush
  apply (cancel_mono (s.iso.hom.app (unit Λ' (ProjectiveLine Y)))).mp
  apply (cancel_mono (R.R.map
    (((Mod.comap (coefficientMap a (ProjectiveLine Y))).mapDerivedCategorySingleFunctor
      0).hom.app U'))).mp
  simp only [Category.assoc, Functor.map_comp]
  have hcancel :
      R.R.map (((Mod.comap (coefficientMap a (ProjectiveLine Y))).mapDerivedCategorySingleFunctor
        0).inv.app U') ≫
      R.R.map (((Mod.comap (coefficientMap a (ProjectiveLine Y))).mapDerivedCategorySingleFunctor
        0).hom.app U') = 𝟙 _ := by
    rw [← R.R.map_comp, Iso.inv_hom_id_app, R.R.map_id]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [hcancel]
  erw [Category.comp_id]
  erw [hs]
  have hn := ((Mod.comap (coefficientMap a Y)).mapDerivedCategorySingleFunctor 0).hom.naturality m'
  change (Mod.comap (coefficientMap a Y)).mapDerivedCategory.map
      ((DerivedCategory.singleFunctor (Modules Λ' Y) 0).map m') ≫
        ((Mod.comap (coefficientMap a Y)).mapDerivedCategorySingleFunctor 0).hom.app _ =
    ((Mod.comap (coefficientMap a Y)).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor (Modules Λ Y) 0).map
        ((Mod.comap (coefficientMap a Y)).map m') at hn
  erw [reassoc_of% hn]
  erw [Iso.inv_hom_id_app_assoc]
  erw [← singlePushComparison_naturality R uP.semilinear.hom]
  have hsingle := congrArg (DerivedCategory.singleFunctor (Modules Λ Y) 0).map hm
  simpa only [m, m', f, U, U', Functor.map_comp, Category.assoc] using
    congrArg (fun k => k ≫ singlePushComparison R
      ((Mod.comap (coefficientMap a (ProjectiveLine Y))).obj U')) hsingle

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
