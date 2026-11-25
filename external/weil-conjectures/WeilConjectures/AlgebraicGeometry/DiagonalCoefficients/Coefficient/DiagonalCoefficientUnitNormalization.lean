/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteComparison
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedPadicTorsionLinearity

/-! # Constant coefficient and unit normalization

Source: diagonal tower coefficient changes (1), scalar units and finite constants.
(blueprint: lem-diagonal-coefficient-unit-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local semireducible] UniformizerSquareData.cyclicEndpoints
  UniformizerSquareData.quotientEndpoints

attribute [local instance] UniformizerSquareData.inverse_additive
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem constant_forget_generator
    (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) (V : X.ProEtᵒᵖ) (b : B) :
    (finiteConstantAbComparison B X).hom.hom.app V
        (((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of B B))).app V) b) =
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of B))).app V) b := by
  let J := Scheme.ProEt.topology X
  let U := forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1}
  let P := (Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of B B)
  let : J.PreservesSheafification U :=
    Sheaf.preservesSheafification_of_adjunction J (ModuleCat.forget₂CoinduceAdj B)
  change (((constantCommuteCompose J U).hom.app (ModuleCat.of B B)).hom.app V) _ = _
  rw [constantCommuteCompose_hom_app_hom]
  have hc : (Functor.constComp X.ProEtᵒᵖ (ModuleCat.of B B) U).hom = 𝟙 (P ⋙ U) := rfl
  erw [hc, sheafifyMap_id, Category.comp_id]
  exact congrArg (fun f ↦ (f.app V).hom b) (sheafComposeIso_inv_fac J U P)

private theorem constant_forget_inv_generator
    (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) (V : X.ProEtᵒᵖ) (b : B) :
    (finiteConstantAbComparison B X).inv.hom.app V
        (((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of B))).app V) b) =
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of B B))).app V) b := by
  rw [← constant_forget_generator B X V b]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app V) (finiteConstantAbComparison B X).hom_inv_id) _

private theorem normalized_constant_map
    {B A : Type (u + 1)} [CommRing B] [CommRing A]
    (φ : B →+* A) (X : Scheme.{u})
    (m : geoCartierConstant B X ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj (geoCartierConstant A X))
    (hm : ∀ (V : X.ProEtᵒᵖ) (b : B), m.hom.app V
        (((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of B B))).app V) b) =
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).app V) (φ b)) :
    (finiteConstantAbComparison B X).inv ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).map m ≫
        (finiteConstantAbComparison A X).hom =
      ((sfbConstantRing X).map (RingCat.ofHom φ)).hom := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (finiteConstantAbRing A X).property
  ext V b
  change (finiteConstantAbComparison A X).hom.hom.app V
    (m.hom.app V ((finiteConstantAbComparison B X).inv.hom.app V
      (((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of B))).app V) b))) = _
  erw [constant_forget_inv_generator, hm, constant_forget_generator]
  have h := toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map ((forget₂ RingCat.{u + 1} Ab.{u + 1}).map
      (RingCat.ofHom φ)))
  have h' := congrArg (fun f ↦ (f.app V).hom b) h
  dsimp only [NatTrans.comp_app, Functor.const_map_app] at h'
  change ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app V).hom (φ b) =
    ((sheafifyMap (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (AddCommGrpCat.ofHom φ.toAddMonoidHom))).app V).hom
      (((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of B))).app V).hom b)
  exact h'

open CategoryTheory.MonoidalCategory MonObj in
/-- Maps from the integral coefficient ring into a sheaf killed by a prime power
are determined by their values on the unit.
Source: coefficient changes (1). (blueprint: lem-diagonal-coefficient-unit-normalization).
Proof: the unit and multiplication by the prime power are jointly epimorphic. The
maps agree on the unit by hypothesis, and both vanish after that multiplication. -/
theorem diagonal_padic_unit_ext (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (r : ℕ)
    (T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (hT : (l ^ r) • 𝟙 T = 0)
    (f g : condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X ⟶ T)
    (h : η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X] ≫ f =
      η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X] ≫ g) : f = g := by
  let := epi_unit_and_power l X r
  apply (cancel_epi (biprod.desc
    η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X]
      ((l ^ r) • 𝟙 (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)))).mp
  apply biprod.hom_ext'
  · simpa only [← Category.assoc, biprod.inl_desc] using h
  · simp only [← Category.assoc, biprod.inr_desc, Preadditive.nsmul_comp, Category.id_comp]
    rw [← Category.comp_id f, ← Category.comp_id g, ← Preadditive.comp_nsmul,
      ← Preadditive.comp_nsmul, hT, comp_zero, comp_zero]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
