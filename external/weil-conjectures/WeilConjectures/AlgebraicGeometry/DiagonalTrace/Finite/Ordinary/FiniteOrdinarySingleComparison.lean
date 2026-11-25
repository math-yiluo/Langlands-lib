/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCoefficientModel

/-! # Single comparison in the ordinary coefficient presentation

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-ordinary-single-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃ t₁ t₂ t₃
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100001] finiteOrdinaryDerived finiteOrdinaryExt
  finiteOrdinaryIntrinsicDerived
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
attribute [local implicit_reducible] SpTowerShriek.tau spCoefficientCommRings
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  Etale.ordinaryFiniteDegreeZero Etale.ordinaryFiniteSingleFunctor
  diagonalAbSheafAbelian towerAbelian systemsAbelian

attribute [local instance 100000] CategoryTheory.Abelian.toPreadditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual composite single comparison is unchanged by the cached ordinary
coefficient presentation. Source: exact single-complex comparison
(blueprint: lem-sfb-finite-ordinary-single-comparison).

Proof: unfold nuSingle and the two cached actual functors. Both sides are the
realization image of the comparison single isomorphism, followed by the
realization single isomorphism, so they agree by reflexivity. -/
theorem finiteOrdinarySingleComparison_eq (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})
    (M : OrdinaryEtaleModules (FiniteRing l E n) T) :
    SpTowerP1.nuSingle l E n T M =
      (finiteOrdinaryRealization l E n T).mapDerivedCategory.mapIso
          (((finiteOrdinaryComparison (FiniteRing l E n) T).mapDerivedCategorySingleFunctor
            0).app M) ≪≫
        ((finiteOrdinaryRealization l E n T).mapDerivedCategorySingleFunctor 0).app
          ((finiteOrdinaryComparison (FiniteRing l E n) T).obj M) := by
  rfl

end AlgebraicGeometry.ProEtale.DiagonalTrace
