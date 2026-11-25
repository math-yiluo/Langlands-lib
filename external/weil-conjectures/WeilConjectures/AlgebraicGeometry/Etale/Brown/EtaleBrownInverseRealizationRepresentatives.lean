/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import all WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownImageRealizationDerived
import WeilConjectures.CategoryTheory.Cochain.CochainInverseMateComparison
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ExactLeftCochainTranspose

/-! # Open scalar transport decomposition

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16;
Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

-- The concrete mate comparison elaborates large coefficient category expressions.
/-- The inverse-image realization is the localization of the ordinary comparison.
Source: Zheng Construction 5.15 and Lemma 5.16; Stacks 03CY and 07A4.
(blueprint: lem-pur-etale-brown-inverse-realization-representatives).

Proof: take the ordinary inverse mate of the section-normalized direct comparison.
The underlying set-sheaf adjunction and the algebraic inverse-image Hom formula
identify its components with the section pullback comparison. Constants are preserved,
so this is linear and invertible. Prolong this comparison to cochain complexes.
The normalized direct-image unit equation and the two derived Hom transpose formulas
identify its localization with the inverse derived mate. Cancel the realization
factorizations. The prescribed mate equation for the supplied image realization
identifies that mate with its inverse-image comparison, giving the displayed equation.
The argument uses neither properness nor boundedness. -/
theorem etaleBrownInverseRealization_representatives
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (r : StrictEtaleBrownImageRealization O t g n A B RV RW) :
    ∃ e : (A.lift n).modules ⋙ strictEtaleBrownConstant O t V n ≅
        strictEtaleBrownConstant O t W n ⋙
          Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g,
      letI := RV.val.ordinaryAdditive
      letI := RW.val.ordinaryAdditive
      ∀ K : CochainComplex (strictEtaleLevel W O t n) ℤ,
        r.inverse.inv.app (DerivedCategory.Q.obj K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            g).mapDerivedCategory.map ((RW.factors n).hom.app K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            g).mapDerivedCategoryFactors.hom.app
            (((strictEtaleBrownConstant O t W n).mapHomologicalComplex (.up ℤ)).obj K) =
        (RV.derived n).map (B.inverseFactors.hom.app K) ≫
          (RV.factors n).hom.app (((A.lift n).modules.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  classical
  have := RV.val.ordinaryAdditive
  have := RW.val.ordinaryAdditive
  have : (strictEtaleBrownConstant O t V n).IsEquivalence := constant_equivalence O t V n
  have : (strictEtaleBrownConstant O t W n).IsEquivalence := constant_equivalence O t W n
  let b := Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g
  let G := Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g
  let ηG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
    { app := strictEtaleBrownRightUnit O t g n
      naturality := by
        intro I J f
        change DerivedCategory.Q.map ((G.mapHomologicalComplex _).map f) ≫
            G.rightDerivedFunctorUnitQ J =
          G.rightDerivedFunctorUnitQ I ≫ G.rightDerivedFunctor.map (DerivedCategory.Q.map f)
        exact G.rightDerivedFunctorUnitQ_naturality f }
  exact cochainInverseMate_comparison
    (A := strictEtaleLevel W O t n) (B := strictEtaleLevel V O t n)
    (G := strictEtaleBrownConstant O t W n) (H := strictEtaleBrownConstant O t V n)
    (GD := RW.derived n) (HD := RV.derived n)
    (A.levelAdj n) b B.adjunction b.mapDerivedCategoryRightDerivedAdjunction
    B.inverseFactors
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
      g).mapDerivedCategoryFactors
    B.directUnit ηG (RW.factors n) (RV.factors n)
    B.transpose (Adjunction.derivedCochain_transpose b)
    r.val.ordinaryRight r.right r.inverse r.property.2.1 r.property.2.2

end AlgebraicGeometry
