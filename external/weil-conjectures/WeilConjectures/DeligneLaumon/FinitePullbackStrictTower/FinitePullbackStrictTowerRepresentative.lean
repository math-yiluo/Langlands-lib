/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerComparisonData

/-! # Data for the natural finite pullback comparison of strict reduction towers

Source: Stacks Project, Tags 099N(5), 0G7E, 06XN, 03EL and 0FNH
(blueprint: def-a1-finite-pullback-representative-data).
The positive exponent n+1 is indexed by n : ℕ. The zigzag lives in strict diagrams
before localization. Its two isomorphisms are fixed on tensor generators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a v w a' v' w'
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.FinitePullbackStrictTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The normalized comparison before the integer-shift assertions.
Source: Stacks 099N(5), 03EL and 06XN.
(blueprint: def-a1-finite-pullback-representative-data). -/
structure RepresentativeComparison where
  B : DerivedPair l E Y X (finiteComplex l E g)
  b : pulledReduction l E g ≅ B.functor
  reductionIso : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      (tensorReduction l E Y P ≅ ((reductionComplex l E Y).obj P).asFunctor)
  reduction_normalization : ∀ P hP, ReductionNormalization l E Y P (reductionIso P hP)
  koszulIso : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      ((diagramPull l E g).obj (H l E Y P) ≅ H l E X ((G l E g).obj P))
  koszul_normalization : ∀ P hP, KoszulNormalization l E g P (koszulIso P hP)
  balancedIso : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      (tensorReduction l E X ((G l E g).obj P) ≅ ((finiteComplex l E g).obj P).asFunctor)
  balanced_normalization : ∀ P hP, BalancedNormalization l E g P (balancedIso P hP)
  pull_good : ∀ P, integralOperationsGoodComplex l E Y P →
    integralOperationsGoodComplex l E X ((G l E g).obj P)
  koszul_pull_good : ∀ P, integralOperationsGoodComplex l E Y P →
    ∀ n : ℕ, integralOperationsGoodComplex l E X
      (((diagramPull l E g).obj (H l E Y P)).obj (op n))
  middle_quasiIso : ∀ P, integralOperationsGoodComplex l E Y P →
    ∀ n : ℕ, QuasiIso ((augmentation l E X ((G l E g).obj P)).app (op n))
  reductionH : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      ((reductionPair l E Y).functor.obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj ((transpose l E Y).obj (H l E Y P)))
  reductionH_normalization : ∀ P hP,
    (reductionH P hP).hom ≫
        DerivedCategory.Q.map ((transpose l E Y).map
          (augmentation l E Y P ≫ (reductionIso P hP).hom)) =
      (reductionPair l E Y).counit.app P
  zigzag : ∀ P hP,
    (derivedPull l E g).map (reductionH P hP).hom ≫
        (derivedCounit l E g).app ((transpose l E Y).obj (H l E Y P)) ≫
        DerivedCategory.Q.map ((transpose l E X).map (koszulIso P hP).hom) ≫
        DerivedCategory.Q.map
          ((transpose l E X).map (augmentation l E X ((G l E g).obj P))) ≫
        DerivedCategory.Q.map ((transpose l E X).map (balancedIso P hP).hom) =
      b.hom.app (DerivedCategory.Q.obj P) ≫ B.counit.app P

end WeilConjectures.FinitePullbackStrictTower
