/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientOpenMateQuotient
import WeilConjectures.CategoryTheory.Derived.DerivedExactMateSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-!
# Normalization of the derived supported coefficient restriction mate

Source: Stacks Project, Tags 09XP and 0F1E, the coefficient calculation in
lem-pur-supported-product-localization, step 11.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale

/-- The supported coefficient comparison adjoint to canonical open restriction.
Source: Stacks Tag 09XP
(blueprint: lem-pur-supported-coefficient-derived-open-mate). -/
noncomputable def supportCoefficientOpenMate (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    (supportedCoefficients A d).mapDerivedCategory ⟶
      (supportedCoefficients A b).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory :=
  supportCoefficientMate (supportedCoefficientDerivedAdjunction A b)
    (supportedCoefficientDerivedAdjunction A d)
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
    (derivedSupportTransport A h b d hd)

private theorem exactMap_fac
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (α : F ⟶ G) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.exactDerivedMap α).app (DerivedCategory.Qh.obj K) ≫
        G.mapDerivedCategoryFactorsh.hom.app K =
      F.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K) := by
  simp only [Functor.exactDerivedMap, Localization.liftNatTrans_app,
    Functor.whiskerRight_app, Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem composite_unit_eq
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (G : C' ⥤ D) [G.Additive] :
    Functor.rightDerivedFunctorCompUnit P G ≫
        Functor.whiskerLeft DerivedCategory.Qh (Functor.whiskerRight
          P.rightDerivedFunctorIsoMapDerivedCategory.hom G.rightDerivedFunctor) =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G := by
  apply NatTrans.ext
  funext X
  have h := congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac X
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [Functor.rightDerivedFunctorCompUnit,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  rw [← Functor.map_comp, h]

private theorem pullback_eq_comparison
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (F : C ⥤ D) (G : C' ⥤ D) [F.Additive] [G.Additive]
    (α : F ⟶ P ⋙ G)
    (e : (P ⋙ G).rightDerivedFunctor ≅ P.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (he : (P ⋙ G).rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh e.hom =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G) :
    Functor.rightDerivedPullback P α = Functor.rightDerivedFunctorNatTrans α ≫ e.hom := by
  apply Functor.rightDerived_ext F.rightDerivedFunctor F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  simp only [Functor.whiskerLeft_comp, ← Category.assoc]
  rw [show F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedPullback P α) =
      Functor.rightDerivedPullbackAux P α by simp [Functor.rightDerivedPullback]]
  rw [show F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorNatTrans α) =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory α (.up ℤ)) DerivedCategory.Qh ≫
        (P ⋙ G).rightDerivedFunctorUnit by
      exact Functor.rightDerivedNatTrans_fac _ _ _ _ _ _]
  rw [Category.assoc, he]
  apply NatTrans.ext
  funext X
  simp [Functor.rightDerivedPullbackAux,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit]

private theorem support_pullback_eq (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    Functor.rightDerivedPullback (upperStar (ModuleCat.{u + 1} A) h)
      (supportTransport A h b d hd) = derivedSupportTransport A h b d hd := by
  apply pullback_eq_comparison
  exact (exists_unique_supportTransportComparison A h d).choose_spec.1 |>.trans
    (composite_unit_eq _ _)

end AlgebraicGeometry.Etale
