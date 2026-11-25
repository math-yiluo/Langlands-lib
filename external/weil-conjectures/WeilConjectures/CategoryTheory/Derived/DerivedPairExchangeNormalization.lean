/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement

/-!
# Representative normalization for a square of derived functor pairs

Source: blueprint finite exchange before Rlim; Stacks Tag 06YY.
(blueprint: def-cbc-derived-pair-exchange-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory.Limits

namespace CategoryTheory

/-- The inverse exchange commutes with the actual complex-level derived counits.
Source: blueprint finite exchange before Rlim; Stacks Tag 06YY
(blueprint: def-cbc-derived-pair-exchange-normalization).
The construction is the representative equation itself, quantified over the
specified resolving class. No replacement or derived functor is chosen here. -/
def DerivedPairExchangeNormalization
    {B C T V : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [Category T] [Abelian T] [Category V] [Abelian V]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory T] [HasDerivedCategory V]
    (F : B ⥤ T) [F.Additive] (G : C ⥤ V) [G.Additive]
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (H : T ⥤ V) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (LF : DerivedCategory B ⥤ DerivedCategory T)
    (LG : DerivedCategory C ⥤ DerivedCategory V)
    (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : F ⋙ H ⟶ P ⋙ G) (M : CochainComplex B ℤ → Prop)
    (b : P.mapDerivedCategory ⋙ LG ≅ LF ⋙ H.mapDerivedCategory) : Prop :=
  ∀ K : CochainComplex B ℤ, M K → HEq
    (b.inv.app (DerivedCategory.Q.obj K) ≫
      LG.map (P.mapDerivedCategoryFactors.hom.app K) ≫
      Functor.leftDerivedCounitOnComplex G LG εG
        ((P.mapHomologicalComplex (.up ℤ)).obj K))
    (H.mapDerivedCategory.map (Functor.leftDerivedCounitOnComplex F LF εF K) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((e.mapHomologicalComplex (.up ℤ)).app K))

end CategoryTheory
