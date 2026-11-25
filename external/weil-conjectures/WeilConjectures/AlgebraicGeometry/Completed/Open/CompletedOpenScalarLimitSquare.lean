/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons
import all WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenScalarLimitCoherence

set_option linter.privateModule false

/-! Coherence of exact functors with the constant-diagram mate. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint limit
namespace CategoryTheory

variable {A B C D : Type*}
  [Category A] [Abelian A] [HasLimits A] [HasDerivedCategory A]
  [Category B] [Abelian B] [HasLimits B] [HasDerivedCategory B]
  [Category C] [Abelian C] [HasLimits C] [HasDerivedCategory C]
  [Category D] [Abelian D] [HasLimits D] [HasDerivedCategory D]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]

private abbrev tower {E E' : Type*} [Category E] [Category E'] (V : E ⥤ E') :=
  (Functor.whiskeringRight ℕᵒᵖ E E').obj V

omit [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)] in
private theorem constantSquare (e : F ⋙ G ≅ H ⋙ K) (X : DerivedCategory A) :
    (Functor.const ℕᵒᵖ : D ⥤ _).mapDerivedCategory.map
        ((cbcDerivedSquare F G H K e).inv.app X) ≫
      (UnboundedExactTower.constantInterchange G).inv.app (F.mapDerivedCategory.obj X) ≫
      (tower G).mapDerivedCategory.map
        ((UnboundedExactTower.constantInterchange F).inv.app X) =
    (UnboundedExactTower.constantInterchange K).inv.app (H.mapDerivedCategory.obj X) ≫
      (tower K).mapDerivedCategory.map
        ((UnboundedExactTower.constantInterchange H).inv.app X) ≫
      (cbcDerivedTowerSquare F G H K e).inv.app
        ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj X) := by
  have h := UnboundedExactTower.constant_cube H G F K e X
  have he :
      (tower G).mapDerivedCategory.mapIso ((UnboundedExactTower.constantInterchange F).app X) ≪≫
        (UnboundedExactTower.constantInterchange G).app (F.mapDerivedCategory.obj X) ≪≫
        (Functor.const ℕᵒᵖ : D ⥤ _).mapDerivedCategory.mapIso
          ((cbcDerivedSquare F G H K e).app X) =
      (cbcDerivedTowerSquare F G H K e).app
          ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj X) ≪≫
        (tower K).mapDerivedCategory.mapIso ((UnboundedExactTower.constantInterchange H).app X) ≪≫
        (UnboundedExactTower.constantInterchange K).app (H.mapDerivedCategory.obj X) := by
    apply Iso.ext
    exact h
  have hi := congrArg (fun z ↦ z.inv) he
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hi

private def constAdj {E : Type*} [Category E] [Abelian E] [HasLimits E]
    [HasDerivedCategory E] [HasDerivedCategory (ℕᵒᵖ ⥤ E)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E)] :=
  letI : (lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive :=
    Functor.additive_of_preserves_binary_products _
  (constLimAdj : (Functor.const ℕᵒᵖ : E ⥤ _) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction

private def limitMap {E E' : Type*} [Category E] [Abelian E] [HasLimits E]
    [Category E'] [Abelian E'] [HasLimits E']
    [HasDerivedCategory E] [HasDerivedCategory E']
    [HasDerivedCategory (ℕᵒᵖ ⥤ E)] [HasDerivedCategory (ℕᵒᵖ ⥤ E')]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E')]
    (V : E ⥤ E') [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V] :=
  letI : (lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : (lim : (ℕᵒᵖ ⥤ E') ⥤ E').Additive :=
    Functor.additive_of_preserves_binary_products _
  (mateEquiv (constAdj (E := E)) (constAdj (E := E'))
    (TwoSquare.mk _ _ _ _ (UnboundedExactTower.constantInterchange V).inv))

attribute [local instance] Functor.additive_of_preserves_binary_products

end CategoryTheory

namespace AlgebraicGeometry.Scheme
universe t
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

end AlgebraicGeometry.Scheme
