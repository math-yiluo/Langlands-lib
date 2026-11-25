/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Additive derived stalk cohomology along a scheme isomorphism

Source: Stacks Project, Tags 0098 and 0D5S.
(blueprint: lem-pc-iso-pullback-stalk-cohomology).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The two left adjoints to module pushforward agree canonically.
Source: Stacks Project, Tag 0096.
(blueprint: lem-pc-iso-pullback-stalk-cohomology). -/
def tensorPullbackRestrictIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] :
    Scheme.Modules.tensorPullback j ≅ Scheme.Modules.restrictFunctor j :=
  Adjunction.leftAdjointUniq
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j))
    (Scheme.Modules.restrictAdjunction j)

/-- Tensor pullback along an isomorphism is an equivalence.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-iso-pullback-stalk-cohomology). -/
instance tensorPullbackIsEquivalence {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j] :
    (Scheme.Modules.tensorPullback j).IsEquivalence := by
  let F := Scheme.Modules.restrictFunctor j
  let G := Scheme.Modules.restrictFunctor (inv j)
  let η : 𝟭 Z.Modules ≅ F ⋙ G :=
    (Scheme.Modules.restrictFunctorId).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (IsIso.inv_hom_id j).symm) ≪≫
        Scheme.Modules.restrictFunctorComp (inv j) j
  let ε : G ⋙ F ≅ 𝟭 Y.Modules :=
    (Scheme.Modules.restrictFunctorComp j (inv j)).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (IsIso.hom_inv_id j) ≪≫
        Scheme.Modules.restrictFunctorId
  let e := CategoryTheory.Equivalence.mk F G η ε
  have : F.IsEquivalence := e.isEquivalence_functor
  exact Functor.isEquivalence_of_iso (tensorPullbackRestrictIso j).symm

/-- Exact tensor pullback along an isomorphism has an invertible universal counit.
Source: Stacks Project, Tags 0098 and 0D5S.
(blueprint: lem-pc-iso-pullback-stalk-cohomology). -/
instance isoPullbackCounitIsIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j] :
    IsIso (counit j) := by
  let : HasDerivedCategory.{w} Z.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  have : (derivedPullback j).IsLeftDerivedFunctor (counit j)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)) :=
    (Classical.choose
      (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition))) j
  apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (W := HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ))
    (derivedPullback j) (counit j)
  intro P Q a ha
  have : IsIso (DerivedCategory.Qh.map a) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)) a ha
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.tensorPullback j).mapDerivedCategoryFactorsh a).1 (by
      change IsIso ((Scheme.Modules.tensorPullback j).mapDerivedCategory.map
        (DerivedCategory.Qh.map a))
      infer_instance)

/-- The additive stalk comparison before passing to complexes.
Source: Stacks Project, Tag 0098.
(blueprint: lem-pc-iso-pullback-stalk-cohomology). -/
def isoPullbackAdditiveStalkIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j] (y : Y) :
    RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y) ⋙
        forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u} ≅
      Scheme.Modules.tensorPullback j ⋙
        RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙
          forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u} := by
  exact (Scheme.Modules.restrictStalkNatIso j y).symm ≪≫
    Functor.isoWhiskerRight (tensorPullbackRestrictIso j).symm
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙
        forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u})

/-- Exact forgetting of scalars commutes with homology.
Source: Stacks Project, Tag 0098; exactness of restriction of scalars.
(blueprint: lem-pc-iso-pullback-stalk-cohomology). -/
def complexForgetHomologyIso (R₀ : Type u) [CommRing R₀] (i : ℤ) :
    (forget₂ (ModuleCat.{u} R₀) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor _ (.up ℤ) i ≅
      HomologicalComplex.homologyFunctor _ (.up ℤ) i ⋙
        forget₂ (ModuleCat.{u} R₀) AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun K ↦ (K.sc i).mapHomologyIso (forget₂ (ModuleCat.{u} R₀) AddCommGrpCat.{u}))
    (fun a ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map a)
      (forget₂ (ModuleCat.{u} R₀) AddCommGrpCat.{u}))

/-- The additive derived stalk cohomology functor is induced by ordinary stalk homology.
Source: Stacks Project, Tag 0098.
(blueprint: lem-pc-iso-pullback-stalk-cohomology). -/
def additiveStalkCohomologyFactors (Y : Scheme.{u}) (y : Y) (i : ℤ) :
    DerivedCategory.Q ⋙ comparisonStalkCohomology Y y i ⋙
        forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u} ≅
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙
        forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℤ) ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace y
  let F := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (Y.presheaf.stalk y)) i
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerRight S.mapDerivedCategoryFactors H ≪≫
        Functor.isoWhiskerLeft (S.mapHomologicalComplex (.up ℤ))
          (DerivedCategory.homologyFunctorFactors _ i)) F ≪≫
    Functor.isoWhiskerLeft (S.mapHomologicalComplex (.up ℤ))
      (complexForgetHomologyIso (Y.presheaf.stalk y) i).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (S ⋙ F)) (.up ℤ))
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i)

/-- The universal counit, including the quotient localization factors.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-iso-pullback-stalk-cohomology). -/
def isoPullbackComplexCounitIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j] :
    DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ⋙
        derivedPullback j ≅
      (Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)) := by
  let : HasDerivedCategory.{w} Z.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)
  let E := Scheme.Modules.tensorPullback j
  exact Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))).symm (derivedPullback j) ≪≫
    Functor.isoWhiskerLeft q (asIso (counit j)) ≪≫
    Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (E.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))

/-- Additive derived stalk cohomology commutes with pullback along a scheme isomorphism.
The construction lifts the restriction-stalk isomorphism through localization using
exactness and the specified universal pullback counit.
Source: Stacks Project, Tags 0098 and 0D5S.
(blueprint: lem-pc-iso-pullback-stalk-cohomology). -/
def isoPullbackStalkCohomologyIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j]
    (y : Y) (i : ℤ) :
    comparisonStalkCohomology Z (j y) i ⋙
        forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u} ≅
      derivedPullback j ⋙ comparisonStalkCohomology Y y i ⋙
        forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u} := by
  have : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive :=
    comparisonStalkAdditive Y y
  have : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
  let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙
    forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i
  let E := Scheme.Modules.tensorPullback j
  let e : DerivedCategory.Q ⋙ comparisonStalkCohomology Z (j y) i ⋙
        forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u} ≅
      DerivedCategory.Q ⋙ derivedPullback j ⋙ comparisonStalkCohomology Y y i ⋙
        forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u} :=
    additiveStalkCohomologyFactors Z (j y) i ≪≫
      Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (isoPullbackAdditiveStalkIso j y) (.up ℤ)) H ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ S)) (.up ℤ)).symm H ≪≫
      Functor.isoWhiskerLeft (E.mapHomologicalComplex (.up ℤ))
        (additiveStalkCohomologyFactors Y y i).symm ≪≫
      Functor.isoWhiskerRight (isoPullbackComplexCounitIso j).symm
        (comparisonStalkCohomology Y y i ⋙
          forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u})
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)) _ _ _ _ e

end AlgebraicGeometry.SingleComplexBaseChange
