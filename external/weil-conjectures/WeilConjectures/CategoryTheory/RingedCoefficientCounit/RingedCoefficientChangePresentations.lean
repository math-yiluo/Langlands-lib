/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedCoefficientCounit.RingedCoefficientCounitPresentations

set_option linter.privateModule false

/-!
# Coefficient changes of normalized counit diagrams

Source: Stacks, Tags 03D7, 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations).
Ordinary maps are fixed on sections; derived maps are fixed by localization and
K-flat/K-injective representative equations. No counit identity is a field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v r w u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace CategoryTheory.RingedCoefficientCounit

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [UnivLE.{max u v, r}] [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
  [JX.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JX.HasSheafCompose (forget AddCommGrpCat.{r})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{r})]
  [HasSheafify JX AddCommGrpCat.{r}] [JX.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify JY AddCommGrpCat.{r}] [JY.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify JX CommRingCat.{r}] [HasWeakSheafify JY CommRingCat.{r}]
  {A : CommRingCat.{r}} {RX RI : Sheaf JX CommRingCat.{r}}
  {RY : Sheaf JY CommRingCat.{r}}
  {inverse : Sheaf JY (Type r) ⥤ Sheaf JX (Type r)}
  {direct : Sheaf JX (Type r) ⥤ Sheaf JY (Type r)} {geom : inverse ⊣ direct}
  {IA : SheafOfModules.AlgebraicInverseImage inverse (constantRing JY A) (constantRing JX A)}
  {IR : SheafOfModules.AlgebraicInverseImage inverse RY RI} {c : RI ⟶ RX}

variable [IA.modules.Additive]
  {aX : constantRing JX A ⟶ RX} {aY : constantRing JY A ⟶ RY}
  {aI : constantRing JX A ⟶ RI}
  {o : OrdinaryPresentation direct geom IA IR c aX aY aI}
  [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
  [HasDerivedCategory.{w} (modules (constantRing JX A))]
  [HasDerivedCategory.{w} (modules (constantRing JY A))]

variable {RX' RI' : Sheaf JX CommRingCat.{r}} {RY' : Sheaf JY CommRingCat.{r}}
  {IR' : SheafOfModules.AlgebraicInverseImage inverse RY' RI'} {c' : RI' ⟶ RX'}
  {aX' : constantRing JX A ⟶ RX'} {aY' : constantRing JY A ⟶ RY'}
  {aI' : constantRing JX A ⟶ RI'}
  {o' : OrdinaryPresentation direct geom IA IR' c' aX' aY' aI'}
  [HasDerivedCategory.{w} (modules RX')] [HasDerivedCategory.{w} (modules RY')]

end CategoryTheory.RingedCoefficientCounit
