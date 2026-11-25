/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Product-projection exchange definitions

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-tf-independent-base-change/det-tf-ibc-pasting.md, order 3437;
Stacks Project, Tag 0E46 (blueprint: lemma-base-change-along-product-projection--1).

The helpers specialize the published ambient exchange and construct its canonical
right-adjoint composition maps. The supplied factorization is written as `j ≫ p`.
Declaration ownership: (blueprint: compactification-product-exchange-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Fix the intrinsic pro-etale localization, which uses the standard derived category.
attribute [local instance 50000] proEtaleRingModules_hasDerivedCategory

/-- The ambient unit--square--counit exchange for the product with `T`.
The chosen square is the universal product square, forgotten from schemes over the base;
all four scalar identifications are the published constant-section comparisons.
Source: blueprint order 3437, first displayed arrow; Stacks Tag 0E46
(blueprint: lemma-base-change-along-product-projection--1). -/
def compactificationProductExchange (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (T : Over S) :
    (proEtaleConstantRingPushforward A f.left).rightDerivedFunctor ⋙
        proEtaleConstantRingDerivedPullback A (prod.fst : Y ⨯ T ⟶ Y).left ⟶
      proEtaleConstantRingDerivedPullback A (prod.fst : X ⨯ T ⟶ X).left ⋙
        (proEtaleConstantRingPushforward A (prod.map f (𝟙 T)).left).rightDerivedFunctor :=
  proEtaleAmbientRingedExchange
    { toCommSq := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).toCommSq
      isoPullback := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).isoPullback
      hom_fst := ((IsPullback.of_prod_fst_with_id f T).map
        (Over.forget S)).isoPullback_hom_fst
      hom_snd := ((IsPullback.of_prod_fst_with_id f T).map
        (Over.forget S)).isoPullback_hom_snd }
    (proEtaleConstantRing X.left A) (proEtaleConstantRing Y.left A)
    (proEtaleConstantRing (X ⨯ T).left A) (proEtaleConstantRing (Y ⨯ T).left A)
    (proEtaleConstantRingComparison f.left A)
    (proEtaleConstantRingComparison (prod.fst : Y ⨯ T ⟶ Y).left A)
    (proEtaleConstantRingComparison (prod.fst : X ⨯ T ⟶ X).left A)
    (proEtaleConstantRingComparison (prod.map f (𝟙 T)).left A)
    ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq
      (prod.fst : X ⨯ T ⟶ X).left f.left A)).trans
      ((congr_arg_heq
        (fun q : (X ⨯ T).left ⟶ Y.left ↦ proEtaleConstantRingComparison q A)
        ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).w).trans
        (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq
          (prod.map f (𝟙 T)).left (prod.fst : Y ⨯ T ⟶ Y).left A)).symm))

end AlgebraicGeometry.Scheme
