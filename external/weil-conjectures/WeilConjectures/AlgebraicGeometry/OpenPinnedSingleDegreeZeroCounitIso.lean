/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

/-! # Constructed tensor restriction comparisons
Source: Stacks Project, Tags 08DW and 08HY.
(blueprint: def-pc-open-pinned-single-tensor-restriction-iso). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- The underived open tensor pullback comparison, using the pinned adjunction.
Source: Stacks Project, Tag 08DW.
(blueprint: def-pc-open-pinned-single-tensor-restriction-iso). -/
def openPinnedTensorOpenIso (X : Scheme.{u}) (U : X.Opens) :
    Scheme.Modules.tensorPullback U.ι ≅ schemeOpenRestriction X U :=
  (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm ≪≫
    (Scheme.Modules.overFunctorEquiv U).symm

/-- Tensor restriction comparison constructed from composition comparisons.
Source: Stacks Project, Tags 08DW and 08HY.
(blueprint: def-pc-open-pinned-single-tensor-restriction-iso). -/
def openPinnedTensorRestrictionIso
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) :
    Scheme.Modules.tensorPullback k ⋙ schemeOpenRestriction X' U' ≅
      schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback j :=
  Functor.isoWhiskerLeft _ (openPinnedTensorOpenIso X' U').symm ≪≫
    (Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl).symm ≪≫
    Scheme.Modules.tensorPullbackCompositionIso j U.ι (U'.ι ≫ k) hj ≪≫
    Functor.isoWhiskerRight (openPinnedTensorOpenIso X U) _

/-- The target comparison on single complexes, constructed without choosing data.
Source: Stacks Project, Tags 08DW and 08HY.
(blueprint: def-pc-open-pinned-single-tensor-restriction-iso). -/
def openPinnedSingleTargetRestrictionIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) :
    (Scheme.Modules.tensorPullback k ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0) ⋙
          (schemeOpenRestriction X' U').mapDerivedCategory ≅
        schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback j ⋙
          DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace)) 0 :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((schemeOpenRestriction X' U').mapDerivedCategorySingleFunctor 0) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openPinnedTensorRestrictionIso k U U' j hj) _ ≪≫
    Functor.associator _ _ _

/-- Termwise tensor restriction comparison on the homotopy categories.
Source: Stacks Project, Tags 08DW and 08HY.
(blueprint: def-pc-open-pinned-single-tensor-restriction-iso). -/
def openPinnedHomotopyTensorRestrictionIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) :
    (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
        (schemeOpenRestriction X' U').mapHomotopyCategory (.up ℤ) ≅
      (schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback j).mapHomotopyCategory (.up ℤ) :=
  by
    dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
    letI := schemeOpenRestriction_additive X U
    letI := schemeOpenRestriction_additive X' U'
    let mapSquare {C D B E : Type (u + 1)}
        [Category.{u} C] [Category.{u} D] [Category.{u} B] [Category.{u} E]
        [Preadditive C] [Preadditive D] [Preadditive B] [Preadditive E]
        {F : C ⥤ D} {G : D ⥤ E} {R : C ⥤ B} {J : B ⥤ E}
        [F.Additive] [G.Additive] [R.Additive] [J.Additive]
        (e : F ⋙ G ≅ R ⋙ J) :
        F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ) ≅
          R.mapHomotopyCategory (.up ℤ) ⋙ J.mapHomotopyCategory (.up ℤ) :=
      Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm
    exact mapSquare (openPinnedTensorRestrictionIso k U U' j hj)

end AlgebraicGeometry
