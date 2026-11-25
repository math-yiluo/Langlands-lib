/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareSupplement
import WeilConjectures.SixFunctors.BaseChange.Pasting
public import WeilConjectures.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange

/-!
# Derived extension-by-zero base change

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
proposition-extension-zero-restriction-closed-subscheme--11; Stacks Tags 03S6, 0F70 and 015F
(blueprint: proposition-extension-zero-restriction-closed-subscheme--11).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

section DerivedTools

open CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedNatIso_symm {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryPlusNatIso e.symm =
      (Functor.mapDerivedCategoryPlusNatIso e).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply DerivedCategory.Plus.ι.map_injective
  simp only [ObjectProperty.ι_obj, Functor.mapDerivedCategoryPlusNatIso,
    Functor.mapDerivedCategoryPlusCompatibility, Functor.mapDerivedCategoryNatIso,
    Localization.liftNatIso, NatIso.mapHomologicalComplex, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Iso.refl_symm, Iso.refl_trans,
    Functor.fullyFaithfulCancelRight_hom_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.refl_hom, NatTrans.comp_app, Functor.comp_obj, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.ι_map, Functor.fullyFaithfulCancelRight_inv_app, Iso.trans_inv,
    Iso.refl_inv, Functor.isoWhiskerLeft_inv, Category.id_comp]
  congr 2
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedId_fac (L : C ⥤ C) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : L ≅ 𝟭 C) (K : HomotopyCategory.Plus C) :
    (Functor.mapDerivedCategoryPlusNatIso e ≪≫
      Functor.mapDerivedCategoryPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
    L.mapDerivedCategoryPlusFactorsh.hom.app K ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  rw [Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem square_identity
    (R : C ⥤ D) (G : D ⥤ D) (L : C ⥤ C)
    [R.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (q : R ⋙ G ≅ L ⋙ R) (eL : L ≅ 𝟭 C) (eG : G ≅ 𝟭 D)
    (hq : ∀ X, q.hom.app X ≫ R.map (eL.hom.app X) = eG.hom.app (R.obj X))
    (K : DerivedCategory.Plus C) :
    (Functor.mapDerivedCategoryPlusSquareIso R G L R q).hom.app K ≫
      R.mapDerivedCategoryPlus.map ((Functor.mapDerivedCategoryPlusNatIso eL ≪≫
        Functor.mapDerivedCategoryPlusIdIso C).hom.app K) =
      (Functor.mapDerivedCategoryPlusNatIso eG ≪≫
        Functor.mapDerivedCategoryPlusIdIso D).hom.app (R.mapDerivedCategoryPlus.obj K) := by
  let eLD := Functor.mapDerivedCategoryPlusNatIso eL ≪≫
    Functor.mapDerivedCategoryPlusIdIso C
  let eGD := Functor.mapDerivedCategoryPlusNatIso eG ≪≫
    Functor.mapDerivedCategoryPlusIdIso D
  have hn : (Functor.mapDerivedCategoryPlusSquareIso R G L R q).hom ≫
      Functor.whiskerRight eLD.hom R.mapDerivedCategoryPlus =
      Functor.whiskerLeft R.mapDerivedCategoryPlus eGD.hom := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)
    intro X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [← cancel_mono (R.mapDerivedCategoryPlusFactorsh.hom.app X)]
    have hnat := eGD.hom.naturality (R.mapDerivedCategoryPlusFactorsh.hom.app X)
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at hnat
    rw [Category.assoc, ← hnat]
    dsimp only [eLD, eGD]
    rw [derivedId_fac, derivedId_fac, Functor.map_comp, Category.assoc]
    have hnR := R.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus eL.hom).app X)
    dsimp only [Functor.comp_map] at hnR
    erw [hnR]
    erw [reassoc_of% (Functor.mapDerivedCategoryPlusSquareIso_fac R G L R q X)]
    congr 2
    rw [← DerivedCategory.Plus.Qh.map_comp]
    congr 1
    apply (HomotopyCategory.Plus.ι D).map_injective
    simp only [Functor.map_comp, NatTrans.ι_map_mapHomotopyCategoryPlus_app]
    obtain ⟨⟨P⟩, hP⟩ := X
    change (HomotopyCategory.quotient D (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app P) ≫
      (R.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient C (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eL.hom (.up ℤ)).app P)) =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex eG.hom (.up ℤ)).app
          ((R.mapHomologicalComplex (.up ℤ)).obj P))
    rw [Functor.mapHomotopyCategory_map, ← Functor.map_comp]
    congr 1
    apply HomologicalComplex.Hom.ext
    funext i
    exact hq (P.X i)
  exact NatTrans.congr_app hn K

end DerivedTools

section Underived

variable (A : Type*) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

end Underived

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The canonical composition comparison for exact extension by zero on `D⁺`.
Source: Stacks 03D8 and 015F, obtained by localizing `openImmersionLowerShriekComp`
(blueprint: proposition-extension-zero-restriction-closed-subscheme--11). -/
noncomputable def extensionZeroCompDerivedPlusIso
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    ((k)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
        ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      ((k ≫ j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k j).symm

end AlgebraicGeometry.Etale
