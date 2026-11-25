/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingCompactification

/-! # Finite discrete coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

private def encodingPullbackIso {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.upperStar (coefficient A) f ⋙ (eU.ordinary.trans eU.fixed).functor ≅
      (eT.ordinary.trans eT.fixed).functor ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let R := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let i : CondensedRing.lowerStar (coefficient A) f ⋙ ET.functor ≅ EU.functor ⋙ R :=
    encodingPushforwardNatIso A T U f eT eU
  let k := Iso.isoCompInverse (H := ET) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
  let b := (CondensedRing.upperStarLowerStarAdjunction (coefficient A) f).comp
    EU.toAdjunction
  exact (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm

private def encodingOpenShriekIso {T U : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.openImmersionLowerShriek (coefficient A) j ⋙
        (eT.ordinary.trans eT.fixed).functor ≅
      (eU.ordinary.trans eU.fixed).functor ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let i := encodingPullbackIso A j eT eU
  let k := Iso.isoCompInverse (H := EU) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (coefficient A) j).comp ET.toAdjunction
  let b := EU.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

private def encodingDerivedPushforwardIso {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.lowerStar (coefficient A) f
  let G := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.rightDerivedFunctor ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.rightDerivedFunctor
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      F ET.functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso (encodingPushforwardNatIso A T U f eT eU) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso EU.functor G

private def encodingDerivedOpenShriekIso {T U : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.openImmersionLowerShriek (coefficient A) j
  let G := openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.mapDerivedCategory ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.mapDerivedCategory
  exact Functor.mapDerivedCategoryCompIso F ET.functor ≪≫
    Functor.mapDerivedCategoryNatIso (encodingOpenShriekIso A j eT eU) ≪≫
    (Functor.mapDerivedCategoryCompIso EU.functor G).symm

/-- The two compactification composites agree under normalized coefficient encoding.
Source: blueprint coefficient-identification proof, steps 11--12; Stacks Tags 015F and 03EK.
(blueprint: lem-sf-finite-discrete-encoding-compactification).

Proof: on every site object both direct images evaluate the same module on the fibre
product. The coefficient-sections identity identifies the scalar actions, giving the
underived direct-image comparison. The same identity gives the pullback comparison.
For an open immersion the two extensions by zero are left adjoint to the identified
restriction functor; uniqueness of left adjoints gives their natural comparison.
The encodings are exact equivalences and are right adjoint to their exact inverses,
so they preserve K-injective complexes. Compute the right derived direct images on
corresponding K-injective resolutions and descend the termwise comparison. Extension
by zero is exact, so its termwise comparison already computes its derived functor.
Compose the two comparisons, using the given open and proper factors of the very same
compactification. This proves the displayed natural isomorphism without changing or
choosing a compactification. -/
theorem encoding_compactification [Finite A] [DiscreteTopology A]
    (E : ∀ T : Scheme.{u}, Encoding A T)
    (X Y : Scheme.{u}) (f : X ⟶ Y) (c : Compactification f) :
    Nonempty (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
        (E Y).fixedDerived.functor ≅
      (E X).fixedDerived.functor ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c) := by
  exact ⟨Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (encodingDerivedPushforwardIso A c.g (E Y) (E c.Z)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (encodingDerivedOpenShriekIso A c.i (E c.Z) (E X)) _ ≪≫
    Functor.associator _ _ _⟩

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
