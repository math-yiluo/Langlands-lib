/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # A universal computation map for simultaneous integral reduction

The existing canonical augmented tower remains publicly imported. This interface
retains its coefficient-linear strict system before evaluation, with one universal
left-derived computation map. It supplies the strict form required by the closed
projection comparison; a family of isomorphisms after evaluation is insufficient.

## References

* Bhatt--Scholze, Definition 3.5.2, p. 24
* Bhatt--Scholze, Definition 3.5.2
* Stacks 06YY, 06XN, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- A strict reduction and its universal derived computation map. The ordinary
adjunction, quotient maps and pure-tensor unit fix the ordinary construction;
the universal counit fixes the derived construction up to its unique compatible
isomorphism. No family of evaluated derived maps is lifted by choice. -/
structure IntegralStrictReductionModel (W : Scheme.{t}) where
  ordinary : scalarReductionSource.{t, u} l E W ⥤ coefficientSequenceModules.{t, u} l E W
  [additive : ordinary.Additive]
  level : ∀ n : ℕ, ordinary ⋙ coefficientSequenceEvaluation.{t, u} l E W n ≅
    scalarReductionExtension.{t, u} l E W n
  transition : ∀ (M : scalarReductionSource.{t, u} l E W) (m n : ℕ) (h : n ≤ m),
    (coefficientSequenceTransition l E W h).app (ordinary.obj M) ≫
        (normalizedDVRModuleRes l E W h).map ((level n).hom.app M) =
      (level m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M
  augmentation : Functor.const ℕᵒᵖ ⟶ ordinary ⋙ coefficientSequenceRestriction.{t, u} l E W
  augmentation_sections : ∀ (M : scalarReductionSource.{t, u} l E W)
    (n : ℕ) (V : W.ProEtᵒᵖ) (x : M.val.obj V),
    HEq (((augmentation.app M).app (op n)).val.app V x)
      (((level n).inv.app M).val.app V
        (unrestrictedIntegralTensorSection.{t, u} l E W n M V 1 x))
  adjunction : ordinary ⊣ coefficientSequenceRestriction.{t, u} l E W ⋙ lim
  adjunction_projection : ∀ (M : scalarReductionSource.{t, u} l E W) (n : ℕ),
    adjunction.unit.app M ≫
        limit.π ((coefficientSequenceRestriction.{t, u} l E W).obj (ordinary.obj M)) (op n) =
      (augmentation.app M).app (op n)
  reduction : DerivedCategory (scalarReductionSource.{t, u} l E W) ⥤
    coefficientSequenceDerived.{t, u} l E W
  counit : DerivedCategory.Q ⋙ reduction ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : reduction.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (scalarReductionSource.{t, u} l E W) (.up ℤ))
  computes : ∀ P : CochainComplex (scalarReductionSource.{t, u} l E W) ℤ,
    integralOperationsGoodComplex.{t, u} l E W P → IsIso (counit.app P)
  evaluation : ∀ n : ℕ, reduction ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
    coefficientFiniteDerivedExtension l E W n
  evaluation_normalized : ∀ (P : CochainComplex (scalarReductionSource.{t, u} l E W) ℤ)
    (hP : integralOperationsGoodComplex.{t, u} l E W P) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map (counit.app P) ≫
        (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
          ((ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (level n) (.up ℤ)).hom.app P) =
      (evaluation n).hom.app (DerivedCategory.Q.obj P) ≫
        (coefficientFiniteReductionModel l E W P hP.1 n).hom

attribute [instance] IntegralStrictReductionModel.additive

end WeilConjectures
