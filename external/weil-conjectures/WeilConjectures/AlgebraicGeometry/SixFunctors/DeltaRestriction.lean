/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-! # Restriction of the evaluation-transpose double-dual morphism

The comparisons below are normalized by evaluation and by the compact-support counit.
All categories are ordinary unbounded categories of constant-ring module sheaves.

## References

* Stacks Project, Tags 08J9 and 08JB
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true

universe u v w z z'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

/-- Evaluation with the factors in the order DK tensor K. -/
def restrictionDualEvaluation {C : Type z} [Category.{v} C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (adj : ∀ K : C, T.obj K ⊣ H.obj (op K))
    (b : ∀ K L : C, (T.obj K).obj L ≅ (T.obj L).obj K) (Ω K : C) :
    (T.obj ((H.obj (op K)).obj Ω)).obj K ⟶ Ω :=
  (b _ _).hom ≫ (adj K).counit.app Ω

/-- The double-dual arrow is the actual transpose of evaluation. -/
def restrictionDualDelta {C : Type z} [Category.{v} C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (adj : ∀ K : C, T.obj K ⊣ H.obj (op K))
    (b : ∀ K L : C, (T.obj K).obj L ≅ (T.obj L).obj K) (Ω K : C) :
    K ⟶ (dualityDoubleFunctor H Ω).obj K :=
  (adj ((H.obj (op K)).obj Ω)).homEquiv K Ω
    (restrictionDualEvaluation T H adj b Ω K)

end CategoryTheory

open CategoryTheory.MonoidalClosed

namespace CategoryTheory
set_option backward.isDefEq.respectTransparency false
end CategoryTheory

namespace CategoryTheory
set_option backward.isDefEq.respectTransparency false
end CategoryTheory

namespace CategoryTheory
set_option backward.isDefEq.respectTransparency false
end CategoryTheory

namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.DerivedCategory.braidedCategory'
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry

namespace Etale

section
attribute [local instance] _root_.DerivedCategory.braidedCategory'
end

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end Etale

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end ProEtale

end AlgebraicGeometry
