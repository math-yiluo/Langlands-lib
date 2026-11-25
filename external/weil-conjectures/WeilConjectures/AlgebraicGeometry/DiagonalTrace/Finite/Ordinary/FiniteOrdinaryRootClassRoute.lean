/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Scalar.FiniteScalarCoordinateRoutes
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Scalar.FiniteScalarRootRouteEquation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Coefficient.FiniteCoefficientScalarTransport

/-! # Arbitrary ordinary root classes in finite coordinates

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-ordinary-root-class-route).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100001] finiteOrdinaryDerived finiteOrdinaryExt
  finiteOrdinaryIntrinsicDerived
  finiteIntegralAbDerived finiteIntegralAbExt finiteIntegralEtaleDerived finiteIntegralEtaleExt
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
  Functor.mapDerivedCategory Ext.homEquiv HasDerivedCategory.standard
  DerivedCategory.singleFunctors
attribute [local implicit_reducible] diagonalAbSheafAbelian towerAbelian systemsAbelian

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- An ordinary arrow with a scalar root class has the corresponding normalized
finite integral-root route, before any Picard or Kummer specialization.
Source: exact scalar transport and the root-coordinate section equation
(blueprint: lem-sfb-finite-ordinary-root-class-route).

Proof: scalar realization gives the normalized additive class route. Apply
congruence to the given class equation using the actual normalized cohomology
route function. Compose with finiteScalarNormalizedRootRoute_eq. -/
theorem finiteOrdinaryCoordinateArrow_root_class (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})
    {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT)
    (x : Sheaf.H (T.rootsOfUnitySheaf (l ^ (n + 1))) 2)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) T ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) T)⟦(2 : ℤ)⟧)
    (hclass : Etale.ordinaryFiniteClass (FiniteRing l E n) T
      (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (FiniteRing l E n)
        (ULift.ext (coefficient_annihilates l E n))) 2 a =
      Sheaf.H.map (Etale.ordinaryFiniteRootMap (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) T) 2 x) :
    @Eq (FiniteScalarBoundaryArrow l E n T)
      (finiteScalarNormalizedModuleRoute l E n T c a)
      (finiteScalarNormalizedRootRoute l E n T x) := by
  have hc := congrArg (finiteScalarNormalizedCohomologyRoute l E n T c) hclass
  exact (finiteOrdinaryCoordinateArrow_scalar l E n T c a).trans
    (hc.trans (finiteScalarNormalizedRootRoute_eq l E n T c x))

end AlgebraicGeometry.ProEtale.DiagonalTrace
