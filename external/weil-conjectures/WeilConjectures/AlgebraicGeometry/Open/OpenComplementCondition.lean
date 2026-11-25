/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Open-complement cohomological-dimension condition
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The open-complement condition at a finite coefficient ring: higher direct images along
an open immersion vanish above the prescribed bound, and all higher direct images of
constructible coefficient sheaves remain constructible.
-/
def HasOpenComplementCondition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (c : ℕ) : Prop :=
  (∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
      (q : ℤ), (c : ℤ) < q →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj M)))) ∧
    (∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
      IsConstructibleEtaleModuleSheaf F →
      IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F))))

end AlgebraicGeometry.Scheme

end
