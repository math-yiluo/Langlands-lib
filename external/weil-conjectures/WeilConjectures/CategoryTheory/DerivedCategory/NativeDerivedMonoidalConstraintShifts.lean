/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.AssociatorShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.BraidingShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.LeftUnitorShift

/-! # Slotwise shifts of the native derived monoidal constraints

A proved packaging of the existing native associator, unitor and Koszul braiding
shift equations. Source: blueprint maps-used sentence, Stacks 0FPQ and 0FNH.
-/

@[expose] public section
set_option autoImplicit false

universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

attribute [local instance] DerivedCategory.braidedCategory'

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

local instance hasColimitsOfSize_constraintShifts : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]

/-- The three native associator slots, the left unitor and the Koszul braiding commute
with the native integer shift comparisons.
Source: Stacks 0FPQ and 0FNH; blueprint `fix-prop-coherence.proof.md`, maps-used sentence.
(blueprint: lem-pur-native-derived-monoidal-constraint-shifts).

Proof: the native associator shift instances descend the signed cochain associator
through K-flat localization in each slot, and transport along resolving isomorphisms.
The native left-unitor theorem descends the unit-complex equation. The native braiding
shift theorem descends the Koszul chain swap and transports along representative
isomorphisms. These source theorems use precisely the native derived monoidal structure;
assemble their three associator assertions and the two displayed equations. -/
theorem nativeDerivedMonoidalConstraintShifts :
    (∀ K L : DerivedCategory C,
      NatTrans.CommShift (associatorNatTrans₁ (DerivedCategory C) K L) ℤ ∧
      NatTrans.CommShift (associatorNatTrans₂ (DerivedCategory C) K L) ℤ ∧
      NatTrans.CommShift (associatorNatTrans₃ (DerivedCategory C) K L) ℤ) ∧
    (∀ (K : DerivedCategory C) (n : ℤ),
      (((curriedTensor (DerivedCategory C)).obj (𝟙_ _)).commShiftIso n).hom.app K ≫
        (λ_ K).hom⟦n⟧' = (λ_ (K⟦n⟧)).hom) ∧
    (∀ (K L : DerivedCategory C) (n : ℤ),
      (β_ K (L⟦n⟧)).hom ≫
          (((curriedTensor (DerivedCategory C)).flip.obj K).commShiftIso n).hom.app L =
        (((curriedTensor (DerivedCategory C)).obj K).commShiftIso n).hom.app L ≫
          (β_ K L).hom⟦n⟧') :=
  ⟨fun _ _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩,
    leftUnitor_commShift_app C, braiding_hom_commShiftIso_hom_app⟩

end DerivedCategory
