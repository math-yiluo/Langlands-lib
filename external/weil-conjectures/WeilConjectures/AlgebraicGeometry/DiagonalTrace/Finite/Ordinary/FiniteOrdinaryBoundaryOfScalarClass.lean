/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCoordinateArrow
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteKummerIntegralEvaluation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryRootClassRoute
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.FiniteIntegralBoundaryPackaging

/-! # Ordinary Kummer classes in finite coordinates

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-ordinary-boundary-of-scalar-class).
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

/-- Any ordinary line arrow representing the scalar Kummer class satisfies the
finite boundary equation in the specified normalized coordinates.
Source: diagonal-tower trace (1), exact scalar and integral comparisons
(blueprint: lem-sfb-finite-ordinary-boundary-of-scalar-class). -/
theorem finiteOrdinary_boundary_of_scalar_class (T : Scheme.{u}) (k : Kummer l T)
    (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) (L : T.Pic)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) T ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) T)⟦(2 : ℤ)⟧)
    (hclass : Etale.ordinaryFiniteClass (FiniteRing l E n) T
      (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (FiniteRing l E n)
        (ULift.ext (coefficient_annihilates l E n))) 2 a =
      Sheaf.H.map (Etale.ordinaryFiniteRootMap (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) T) 2
          (T.kummerδ₁ (l ^ (n + 1)) hT (Scheme.Pic.toCohomologicalPicardGroup T L))) :
    FiniteKummerBoundary l E T n k L (finiteOrdinaryCoordinateArrow l E n T c a) := by
  let x := T.kummerδ₁ (l ^ (n + 1)) hT (Scheme.Pic.toCohomologicalPicardGroup T L)
  have he := finiteOrdinaryCoordinateArrow_root_class l E n T c x a hclass
  dsimp only [finiteScalarNormalizedModuleRoute, finiteScalarNormalizedRootRoute] at he
  rw [← finiteKummer_integral_evaluation l T k n hT L] at he
  exact finiteKummerBoundary_of_integral_eq l E T n k L _ he

end AlgebraicGeometry.ProEtale.DiagonalTrace
