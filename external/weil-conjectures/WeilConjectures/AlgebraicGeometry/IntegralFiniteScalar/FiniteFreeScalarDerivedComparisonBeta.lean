/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions

import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonBetaNormalization
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonBetaMate

/-! The normalized beta part of the finite-free derived comparison.
-/

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

/--
This is strictly the beta, pullback, and mate conjunct of the
finite-free derived comparison; the independent flatness conjunct is recorded
separately.
-/
theorem finiteFreeScalarDerivedComparison_beta
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hS : S.ShortExact) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X)) :
    ∃ β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
        scalarSixChange a Z ⋙ restriction a Z,
      (∀ Z, AugmentationNormalized a S t Z (β Z)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
          (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
        (scalarSixPull Λ f).map ((β Y).hom.app K) ≫
          (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
            ((scalarSixChange a Y).obj K) ≫
          (restriction a X).map ((D.theta a f).inv.app K) =
        tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y)) K ≫
          ((modelPull Λ S f).hom ⊗ₘ 𝟙 ((scalarSixPull Λ f).obj K)) ≫
          (β X).hom.app ((scalarSixPull Λ f).obj K)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
          (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)),
        (β Y).hom.app ((moduleObjectDerivedPushforward Λ.X f).obj K) ≫
          (restriction a Y).map (gamma D a f K) ≫
          (restrictionPush D a f).hom.app ((scalarSixChange a X).obj K) ≫
          (moduleObjectDerivedPushforward Λ.X f).map ((β X).inv.app K) =
        projection Λ f (DerivedCategory.Q.obj (complex Λ S Y))
          (DerivedCategory.Q.obj (complex Λ S X)) (modelPull Λ S f) K) := by
  have h := finiteFreeScalarDerivedComparison_beta_normalized D a S t hS r e₁ e₂
  rcases h with ⟨β, hβ, hpull⟩
  refine ⟨β, hβ, hpull, ?_⟩
  exact finiteFreeScalarDerivedComparison_beta_mate D a S t β hβ hpull

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
