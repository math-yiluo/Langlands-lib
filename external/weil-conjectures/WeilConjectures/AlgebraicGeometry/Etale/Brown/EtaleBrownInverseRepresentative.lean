/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import all WeilConjectures.CategoryTheory.Cochain.CochainInverseMateComparison
import all WeilConjectures.CategoryTheory.Derived.DerivedMateUnitComparison
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence

/-! # Cochain normalization of the inverse Brown comparison

Source: Zheng, Construction 5.15 and Lemma 5.16; Stacks 07A4 and 0FND.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
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

/-- The ordinary inverse comparison is the mate of the supplied sectionwise direct
comparison. Source: Zheng, Construction 5.15; Stacks 07A4.
(blueprint: lem-pur-etale-brown-inverse-representative). -/
abbrev strictEtaleBrownOrdinaryInverse
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    {RV : StrictEtaleBrownRealization O t V PV}
    {RW : StrictEtaleBrownRealization O t W PW}
    (R : StrictEtaleBrownImageRealization O t g n A B RV RW) :
    strictEtaleBrownConstant O t W n ⋙
        Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g ⟶
      (A.lift n).modules ⋙ strictEtaleBrownConstant O t V n :=
  ((mateEquiv (A.levelAdj n)
    (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)).symm
      (.mk _ _ _ _ R.val.ordinaryRight.hom))

-- The transpose compares all four realization factors.
/-- The inverse Brown comparison is the exact localization of its ordinary mate.
Source: Zheng, Construction 5.15 and Lemma 5.16; Stacks 07A4 and 0FND.
(blueprint: lem-pur-etale-brown-inverse-representative).

Proof: transpose the proposed representative under the derived geometric
adjunction. Naturality moves the localization factor through the derived counit.
The mate equation for R.inverse turns its transpose into R.right followed by the
geometric counit. Apply the specified cochain right-derived-unit equation for
R.right and the normalized transpose for B. On ordinary complexes the
inverse/direct-image adjunction identifies this with the ordinary inverse mate
of R.ordinaryRight. The ordinary geometric transpose and the derived adjunction
unit comparison give the other side. Cancel the invertible localization factors
and apply injectivity of the derived Hom transposition. Thus no scalar-extension
or proper projection invertibility is needed here. -/
theorem strictEtaleBrownInverse_representative
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (R : StrictEtaleBrownImageRealization O t g n A B RV RW)
    (K : CochainComplex (strictEtaleLevel W O t n) ℤ) :
    letI : (strictEtaleBrownConstant O t V n).Additive := RV.val.ordinaryAdditive n
    letI : (strictEtaleBrownConstant O t W n).Additive := RW.val.ordinaryAdditive n
    letI : Functor.PreservesZeroMorphisms
        ((A.lift n).modules ⋙ strictEtaleBrownConstant O t V n) :=
      Functor.preservesZeroMorphisms_comp _ _
    R.inverse.hom.app (DerivedCategory.Q.obj K) ≫
        (RV.derived n).map (B.inverseFactors.hom.app K) ≫
        (RV.factors n).hom.app
          (((A.lift n).modules.mapHomologicalComplex (.up ℤ)).obj K) =
      (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        g).mapDerivedCategory.map ((RW.factors n).hom.app K) ≫
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
          g).mapDerivedCategoryFactors.hom.app
          (((strictEtaleBrownConstant O t W n).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (strictEtaleBrownOrdinaryInverse O t g n A B R) (.up ℤ)).app K) := by
  let : (strictEtaleBrownConstant O t V n).Additive := RV.val.ordinaryAdditive n
  let : (strictEtaleBrownConstant O t W n).Additive := RW.val.ordinaryAdditive n
  have : Functor.PreservesZeroMorphisms
      ((A.lift n).modules ⋙ strictEtaleBrownConstant O t V n) :=
    Functor.preservesZeroMorphisms_comp _ _
  let b := Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g
  have hm : ((mateEquiv B.adjunction b.mapDerivedCategoryRightDerivedAdjunction).symm
      (.mk _ _ _ _ R.right.hom)) = R.inverse.hom :=
    (mateEquiv B.adjunction b.mapDerivedCategoryRightDerivedAdjunction).symm_apply_eq.mpr
      R.property.2.2.symm
  rw [← hm]
  exact CategoryTheory.unitComparison_aux
    (QA := DerivedCategory.Q (C := strictEtaleLevel W O t n))
    (QB := DerivedCategory.Q (C := strictEtaleLevel V O t n))
    (QC := DerivedCategory.Q
      (C := Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))))
    (QD := DerivedCategory.Q
      (C := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))))
    ((A.levelAdj n).mapHomologicalComplex (.up ℤ)) (b.mapHomologicalComplex (.up ℤ))
    B.adjunction b.mapDerivedCategoryRightDerivedAdjunction
    B.inverseFactors.hom
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
      g).mapDerivedCategoryFactors.hom
    B.directUnit
    (CategoryTheory.ExactDerivedSquare.canonicalUnit
      (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g))
    (RW.factors n) (RV.factors n) B.transpose
    (CategoryTheory.ExactDerivedSquare.cochain_hom_formula _ _ b)
    (.mk _ _ _ _ (R.val.ordinaryRight.hom.mapHomologicalComplex (.up ℤ)))
    (.mk _ _ _ _ R.right.hom) R.property.2.1
    ((strictEtaleBrownOrdinaryInverse O t g n A B R).mapHomologicalComplex (.up ℤ))
    (CategoryTheory.cochainMate_unit (A.levelAdj n) b R.val.ordinaryRight.hom) K

end AlgebraicGeometry
