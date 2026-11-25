/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-!
# The derived base change morphism

Consider adjunctions `adj : fU ⊣ fL` and `adj' : f'U ⊣ f'L` of additive functors between abelian
categories with exact left adjoints, and exact functors `gU`, `g'U` forming a square
```
CY ──fU──▶ CX
│          │
gU         g'U
▼          ▼
CY' ─f'U─▶ CX'
```
with an isomorphism `σ : gU ⋙ f'U ≅ fU ⋙ g'U`. In the application the categories are sheaf
categories, `fU ⊣ fL` and `f'U ⊣ f'L` are `f^* ⊣ f_*` and `f'^* ⊣ f'_*` for a cartesian square of
schemes, and `gU`, `g'U` are the pullbacks along the two other sides.

The *derived base change morphism* `R(fL) ⋙ D(gU) ⟶ D(g'U) ⋙ R(f'L)`
(`CategoryTheory.Adjunction.derivedBaseChange`) is the mate of the isomorphism
`D(gU) ⋙ D(f'U) ≅ D(fU) ⋙ D(g'U)` induced by `σ`
(`CategoryTheory.Functor.mapDerivedCategorySquareIso`), under the derived adjunctions
`D(fU) ⊣ R(fL)` and `D(f'U) ⊣ R(f'L)`.
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory.Adjunction

variable {CY CX CY' CX' : Type*} [Category CY] [Category CX] [Category CY'] [Category CX']
  [Abelian CY] [Abelian CX] [Abelian CY'] [Abelian CX']
  [HasDerivedCategory CY] [HasDerivedCategory CX] [HasDerivedCategory CY']
  [HasDerivedCategory CX'] [HasKInjectiveResolutions CX] [HasKInjectiveResolutions CX']
  {fU : CY ⥤ CX} {fL : CX ⥤ CY} {f'U : CY' ⥤ CX'} {f'L : CX' ⥤ CY'}
  {gU : CY ⥤ CY'} {g'U : CX ⥤ CX'}
  [fU.Additive] [fL.Additive] [f'U.Additive] [f'L.Additive] [gU.Additive] [g'U.Additive]
  [PreservesFiniteLimits fU] [PreservesFiniteColimits fU]
  [PreservesFiniteLimits f'U] [PreservesFiniteColimits f'U]
  [PreservesFiniteLimits gU] [PreservesFiniteColimits gU]
  [PreservesFiniteLimits g'U] [PreservesFiniteColimits g'U]
  (adj : fU ⊣ fL) (adj' : f'U ⊣ f'L) (σ : gU ⋙ f'U ≅ fU ⋙ g'U)

/-- The derived base change morphism `R(fL) ⋙ D(gU) ⟶ D(g'U) ⋙ R(f'L)`: the mate of the
isomorphism `D(gU) ⋙ D(f'U) ≅ D(fU) ⋙ D(g'U)` induced by `σ`, under the derived adjunctions
`D(fU) ⊣ R(fL)` and `D(f'U) ⊣ R(f'L)`. -/
noncomputable def derivedBaseChange :
    TwoSquare fL.rightDerivedFunctor g'U.mapDerivedCategory gU.mapDerivedCategory
      f'L.rightDerivedFunctor :=
  mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso σ).hom)

end CategoryTheory.Adjunction
