/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

import WeilConjectures.AlgebraicGeometry.Principal.PrincipalDualizingReduction
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalQuotientInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

set_option linter.privateModule false

/-! # Finite reduction of the specified integral Verdier bidual map -/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
-- Keep the existing derived structures opaque during proof elaboration, as in
-- IntegralCoefficients. These attributes are local to this new proof module.
attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme
attribute [local instance] _root_.DerivedCategory.braidedCategory'
attribute [local instance 2000] CommRing.toRing
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

universe v w

universe uA uB

section AbstractBidual
variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (B : Type uB) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  (X : Scheme.{u})

end AbstractBidual

section IntegralVerdierFiniteSteps
variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ]
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
