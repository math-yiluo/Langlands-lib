/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonAugmentation
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonKFlat
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonNativeTensor

/-! Flatness and augmentation part of the finite-free derived comparison.

This is the first conjunct of `derivedAssertions_of_finite_integral_resolution`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

/-- For a short exact finite-free resolution, the augmentation is a quasi-isomorphism, the
pulled-back complex is K-flat, and the native tensor comparison with it is an isomorphism. -/
theorem finiteFreeScalarDerivedComparison_flatness
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hS : S.ShortExact) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X)) :
    ∀ Z : Scheme.{u}, QuasiIso (augmentation Λ S Z) ∧
      CochainComplex.IsKFlatIndependentCoefficients
        (((ModuleRingedComparison.equivalence Λ.X Z).functor.mapHomologicalComplex
          (.up ℤ)).obj (complex Λ S Z)) ∧
      ∀ C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ,
        IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Z) C) := by
  intro Z
  have hK := finiteFreeScalarDerivedComparison_kflat D a S t hS r e₁ e₂ Z
  refine ⟨finiteFreeScalarDerivedComparison_augmentation D a S t hS r e₁ e₂ Z, hK, ?_⟩
  exact finiteFreeScalarDerivedComparison_nativeTensor D a S t hS r e₁ e₂ Z hK

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
