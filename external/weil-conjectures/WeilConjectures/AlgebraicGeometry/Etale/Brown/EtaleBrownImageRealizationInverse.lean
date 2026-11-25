/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! Inverse mate part of the normalized image realization.

(blueprint: lem-pur-etale-brown-image-realization-inverse)
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

/-- Construction of the inverse comparison by the normalized adjunction mate.
Source: Zheng, Construction 5.15 and Lemma 5.16; Stacks 07A4.
(blueprint: lem-pur-etale-brown-image-realization-inverse).

The mate of the derived comparison is invertible because the supplied Brown
realizations are equivalences; its mate equation is the required normalization.
-/
theorem etaleBrownImageRealization_inverse_exists
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (ordinaryRight : A.right n ⋙ strictEtaleBrownConstant O t W n ≅
      strictEtaleBrownConstant O t V n ⋙
        Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (right : B.direct ⋙ RW.derived n ≅ RV.derived n ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).rightDerivedFunctor)
    (hright :
      letI := RV.val.ordinaryAdditive
      letI := RW.val.ordinaryAdditive
      ∀ K : CochainComplex (strictEtaleLevel V O t n) ℤ,
        (RW.derived n).map (B.directUnit.app K) ≫
            right.hom.app (DerivedCategory.Q.obj K) ≫
            (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
              g).rightDerivedFunctor.map ((RV.factors n).hom.app K) =
          (RW.factors n).hom.app (((A.right n).mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex ordinaryRight.hom (.up ℤ)).app K) ≫
            strictEtaleBrownRightUnit O t g n
              (((strictEtaleBrownConstant O t V n).mapHomologicalComplex
                (.up ℤ)).obj K)) :
    ∃ inverse : RW.derived n ⋙
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).mapDerivedCategory ≅
      B.inverse ⋙ RV.derived n,
      (mateEquiv B.adjunction
        (Etale.upperStarLowerStarAdjunction
          (ModuleCat (strictEtaleBrownRing O t n)) g).mapDerivedCategoryRightDerivedAdjunction
        (.mk _ _ _ _ inverse.hom)) = right.hom := by
  classical
  have _ := hright
  have : (RV.derived n).IsEquivalence := RV.val.equivalence n
  have : (RW.derived n).IsEquivalence := RW.val.equivalence n
  let adj₂ :=
    (Etale.upperStarLowerStarAdjunction
      (ModuleCat (strictEtaleBrownRing O t n)) g).mapDerivedCategoryRightDerivedAdjunction
  let α := ((mateEquiv B.adjunction adj₂).symm
    (.mk _ _ _ _ right.hom))
  have : IsIso α := isIso_inverseMate_of_equivalences B.adjunction adj₂ right
  refine ⟨asIso α, ?_⟩
  exact
    ((mateEquiv B.adjunction adj₂).apply_symm_apply (.mk _ _ _ _ right.hom))

end AlgebraicGeometry
