/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.CategoryTheory.DerivedExactSquare
import WeilConjectures.SixFunctors.BaseChange.Pasting

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

end DerivedTools

section Underived

variable (A : Type*) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

end Underived

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The inverse of the canonical adjunction mate, applied termwise and localized,
restricted to bounded below derived categories. Source: Stacks 03S6, 015F
(blueprint: proposition-extension-zero-restriction-closed-subscheme--11).
The `IsPullback` argument is the property underlying `OpenImmersionSquare`;
its chosen pullback identification does not affect this canonical map. -/
noncomputable def extensionZeroBaseChangeDerivedPlusIso
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) :
    ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
        ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      ((gU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
        ((j')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
        (ModuleCat.{u + 1} Λ) sq)).symm ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

end AlgebraicGeometry.Etale
