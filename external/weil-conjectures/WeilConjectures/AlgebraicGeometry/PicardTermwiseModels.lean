/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

/-! # Termwise Picard models and canonical restriction comparisons

Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: def-sc-picard-termwise-models)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Termwise tensor pullback of the model transported from the open site.
Source: Stacks Project, Tag 06YJ.
(blueprint: def-sc-picard-termwise-models) -/
abbrev picardTermwiseModel (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    {T : Scheme.{v}} (s : T ⟶ U.toScheme) :
    CochainComplex (SheafOfModules.{v} (moduleRings T.toRingedSpace)) ℤ := by
  let : (Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (Modules.tensorPullback s).Additive :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction s)).left_adjoint_additive
  exact ((Modules.tensorPullback s).mapHomologicalComplex (.up ℤ)).obj
    (((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K)

/-- The degree-zero single of the underived pullback of the source structure sheaf.
Source: Stacks Project, Tag 06YJ.
(blueprint: def-sc-picard-termwise-models) -/
abbrev picardTermwiseSource {W T : Scheme.{v}} (t : T ⟶ W) :=
  (CochainComplex.singleFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
      ((Modules.tensorPullback t).obj (SheafOfModules.unit (moduleRings W.toRingedSpace)))

/-- Comparison from the new source single to the termwise pullback of the old one.
Source: Stacks Project, Tags 0096 and 0D5S; Mathlib single-complex comparison.
(blueprint: def-sc-picard-termwise-models) -/
def picardTermwiseSourceRestrictionIso
    {W T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (ht : i ≫ t = t') :
    let : (Modules.tensorPullback i).Additive :=
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
    picardTermwiseSource t' ≅
      ((Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj
        (picardTermwiseSource t) := by
  let : (Modules.tensorPullback i).Additive :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
  exact (CochainComplex.singleFunctor
    (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).mapIso
      ((Modules.tensorPullbackCompositionIso i t t' ht).app
        (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex
      (Modules.tensorPullback i) (.up ℤ) 0).app
        ((Modules.tensorPullback t).obj
          (SheafOfModules.unit (moduleRings W.toRingedSpace)))).symm

/-- Comparison from the new model to the termwise pullback of the old model.
Source: Stacks Project, Tags 0096 and 0D5S; termwise functor composition.
(blueprint: def-sc-picard-termwise-models) -/
def picardTermwiseModelRestrictionIso (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    {T T' : Scheme.{v}} (i : T' ⟶ T) (s : T ⟶ U.toScheme)
    (s' : T' ⟶ U.toScheme) (hs : i ≫ s = s') :
    let : (Modules.tensorPullback i).Additive :=
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
    picardTermwiseModel W U K s' ≅
      ((Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj
        (picardTermwiseModel W U K s) := by
  let : (Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (Modules.tensorPullback i).Additive :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
  let : (Modules.tensorPullback s).Additive :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction s)).left_adjoint_additive
  let : (Modules.tensorPullback s').Additive :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction s')).left_adjoint_additive
  exact ((Functor.mapHomologicalComplexCompIso
    (Modules.tensorPullbackCompositionIso i s s' hs).symm (.up ℤ)).app
      (((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K)).symm

/-- The natural complex counit of tensor pullback, using the counits pinned by the
canonical derived composition theorem. Its data is determined by the left-derived
universal property, rather than by choosing an arbitrary object comparison.
Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: def-sc-picard-termwise-models) -/
def picardTermwiseCounit
    [d : ∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {T T' : Scheme.{v}} (i : T' ⟶ T) :
    let : (Modules.tensorPullback i).Additive :=
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
    DerivedCategory.Q ⋙ derivedPullback i ⟶
      (Modules.tensorPullback i).mapHomologicalComplex (.up ℤ) ⋙ (@DerivedCategory.Q _ _ _
        (d T')) := by
  let a : ∀ {X Y : Scheme.{v}} (f : X ⟶ Y), (Modules.tensorPullback f).Additive :=
    fun f ↦ Classical.choose (exists_derivedPullbackComposition (d := d)) f
  let ε : ∀ {X Y : Scheme.{v}} (f : X ⟶ Y),
      DerivedCategory.Qh ⋙ derivedPullback f ⟶
        (Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙
          (@DerivedCategory.Qh _ _ _ (d X)) :=
    fun f ↦ Classical.choose
      (Classical.choose_spec (exists_derivedPullbackComposition (d := d))) f
  let : (Modules.tensorPullback i).Additive := a i
  let q := HomotopyCategory.quotient
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) (.up ℤ)
  let F := Modules.tensorPullback i
  let Qh' := @DerivedCategory.Qh _ _ _ (d T')
  exact (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm
      (derivedPullback i)).hom ≫
    (Functor.associator q DerivedCategory.Qh (derivedPullback i)).hom ≫
    Functor.whiskerLeft q (ε i) ≫
    (Functor.associator q (F.mapHomotopyCategory (.up ℤ)) Qh').inv ≫
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
      Qh').hom ≫
    (Functor.associator (F.mapHomologicalComplex (.up ℤ))
      (HomotopyCategory.quotient _ (.up ℤ)) Qh').hom ≫
    (Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (@DerivedCategory.quotientCompQhIso _ _ _ (d T'))).hom

end
end AlgebraicGeometry.Scheme
