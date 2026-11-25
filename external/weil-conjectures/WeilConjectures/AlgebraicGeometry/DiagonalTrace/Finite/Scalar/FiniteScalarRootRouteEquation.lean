/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Scalar.FiniteScalarCoordinateRoutes
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Coefficient.FiniteCoefficientRootCoordinate
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteCohomologyMapNormalization

/-! # Arbitrary ordinary root classes in finite coordinates

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-scalar-root-route-equation).
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

/-- The normalized image of root insertion is the integral-root route.
Source: exact cohomology-map naturality and the root section normalization
(blueprint: lem-sfb-finite-scalar-root-route-equation).

Proof: apply finiteCohomologyMap_normalization to the ordinary root map, the
scalar line coordinate, Cartier roots comparison and finiteRootMap. The required
target-map factorization is finiteScalarLineCoordinate_root; the source map is
the actual inverse integer comparison. No ordinary arrow is used here. -/
theorem finiteScalarNormalizedRootRoute_eq (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})
    {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT)
    (x : Sheaf.H (T.rootsOfUnitySheaf (l ^ (n + 1))) 2) :
    @Eq (FiniteScalarBoundaryArrow l E n T)
      (finiteScalarNormalizedCohomologyRoute l E n T c
        (Sheaf.H.map (Etale.ordinaryFiniteRootMap (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext (coefficient_annihilates l E n)) T) 2 x))
      (finiteScalarNormalizedRootRoute l E n T x) := by
  exact finiteCohomologyMap_normalization T
    (Etale.ordinaryFiniteRootMap (FiniteRing l E n) (l ^ (n + 1))
      (ULift.ext (coefficient_annihilates l E n)) T)
    (finiteScalarLineCoordinate l E n T c)
    (cartierRootsComparison T (l ^ (n + 1))) (finiteRootMap l E T n)
    (finiteScalarLineCoordinate_root l E n T c) x
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (integerComparison T).inv)

end AlgebraicGeometry.ProEtale.DiagonalTrace
