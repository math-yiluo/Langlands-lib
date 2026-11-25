/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralQcqsReductionConstructible
import all WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientConstructible
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import all WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedSectionSquares
import WeilConjectures.AlgebraicGeometry.SmoothPurity.EllCoefficientFiber
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CofinalCoefficientProjectionCocone
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

set_option linter.privateModule false

/-! # Constructible cohomology of the evaluated strict reductions

Source: blueprint latest, normalized-towers-reduction, constructibility paragraph;
Stacks Tags 093M, 093U, 06YY, 08J5.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

-- Fix the site universe before imported max-universe coefficient instances are tried.
private local instance (priority := 10000) fixedSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private noncomputable local instance (priority := 10000) fixedRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, 0} X

private noncomputable local instance (priority := 10000) fixedAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} X

private local instance (priority := 10000) fixedLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X

private noncomputable local instance (priority := 10000) fixedModuleAbelian
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :
    Abelian (ringedSiteModules.{u + 1} R) := SheafOfModules.instAbelian R

private local instance positiveUniformizerFinite (j : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (j + 1)) :=
  Padic.finite_coefficientExtensionRing l E (j + 1) (by omega)

end AlgebraicGeometry.ProEtale
