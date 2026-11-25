/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

import WeilConjectures.AlgebraicGeometry.Principal.PrincipalDualizingReduction
import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDualBound

set_option linter.privateModule false

/-! # One finite-level Verdier estimate for integral coefficients -/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme
attribute [local instance] _root_.DerivedCategory.braidedCategory'
attribute [local instance 2000] CommRing.toRing
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

section IntegralVerdierFiniteSteps
variable {Λ : Type (u + 1)} [CommRing Λ]
  {r : Λ} (hr : r ∈ nonZeroDivisors Λ) (m : ℕ) (hm : 1 ≤ m)
  [Finite (Λ ⧸ Ideal.span {r ^ m})] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ Ideal.span {r ^ m}) (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
  [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
  (W : DerivedCategoryModule Λ X)
  (eW : W ≅ (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
    (constantComplex Λ (Spec (.of k))))
  {K : DerivedCategoryModule Λ X} {a b : ℤ}
  (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
    ((reductionModIdeal Λ X (Ideal.span {r ^ m})).obj K))
  (ht : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
    ((reductionModIdeal Λ X (Ideal.span {r ^ m})).obj K))

end IntegralVerdierFiniteSteps
end AlgebraicGeometry.Etale
