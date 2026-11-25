/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonBetaPullbackKFlat
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonBetaPullbackDescent

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

/-! Pullback naturality of a normalized finite-free beta comparison.
-/

/--
The K-flat representative calculation and its descent to the
unbounded derived category are supplied by the two strictly simpler lemmas
imported above.
-/
theorem finiteFreeScalarDerivedComparison_beta_pullback
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z)
    (hβ : ∀ Z, AugmentationNormalized a S t Z (β Z)) :
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
      (scalarSixPull Λ f).map ((β Y).hom.app K) ≫
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((scalarSixChange a Y).obj K) ≫
        (restriction a X).map ((D.theta a f).inv.app K) =
      tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y)) K ≫
        ((modelPull Λ S f).hom ⊗ₘ 𝟙 ((scalarSixPull Λ f).obj K)) ≫
        (β X).hom.app ((scalarSixPull Λ f).obj K) := by
  exact fun X Y f K ↦ finiteFreeScalarDerivedComparison_beta_pullback_of_kflat
    D a S t β hβ (fun X Y f C hC ↦
      finiteFreeScalarDerivedComparison_beta_pullback_kflat D a S t β hβ X Y f C hC)
      X Y f K

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
