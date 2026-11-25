/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonBetaConstruction
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonBetaPullback

/-! Construction and normalization of the finite-free beta comparison.
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
This is the construction, ordinary augmentation normalization, and
pullback part of the beta comparison.
-/
theorem finiteFreeScalarDerivedComparison_beta_normalized
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
          (β X).hom.app ((scalarSixPull Λ f).obj K)) := by
  obtain ⟨β, hβ⟩ := finiteFreeScalarDerivedComparison_beta_construction D a S t hS r e₁ e₂
  refine ⟨β, hβ, ?_⟩
  exact finiteFreeScalarDerivedComparison_beta_pullback D a S t β hβ

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
