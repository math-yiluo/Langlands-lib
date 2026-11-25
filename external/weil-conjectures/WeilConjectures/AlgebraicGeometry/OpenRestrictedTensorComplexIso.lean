/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenDerivedStalkIso
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

/-! # Underived tensor restriction and its derived target transport

Source: Stacks Project, Tags 0D5U and 0D5S, exact restriction and composition.
(blueprint: def-pc-open-restricted-tensor-complex-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- Tensor pullback along an open immersion agrees with exact restriction, with
normalization fixed by the chosen tensor adjunction and the usual pullback adjunction.
Source: Stacks Project, Tag 0D5U.
(blueprint: def-pc-open-restricted-tensor-complex-iso). -/
def openTensorRestrictionIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] :
    Scheme.Modules.tensorPullback j ≅ Scheme.Modules.restrictFunctor j :=
  (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction j) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback j).symm

/-- The termwise restriction comparison, constructed by tensor composition and
open restriction; its orientation is from restriction of pullback to pullback
of restriction. No derived pullback or complex is involved.
Source: Stacks Project, Tags 0097 and 0D5U.
(blueprint: def-pc-open-restricted-tensor-complex-iso). -/
def openTensorRestrictionSquareIso {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens) :
    Scheme.Modules.tensorPullback k ⋙ Scheme.Modules.restrictFunctor (pullback.fst k U.ι) ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.tensorPullback (pullback.snd k U.ι) :=
  Functor.isoWhiskerLeft _ (openTensorRestrictionIso (pullback.fst k U.ι)).symm ≪≫
    (Scheme.Modules.tensorPullbackCompositionIso (pullback.fst k U.ι) k
      (pullback.fst k U.ι ≫ k) rfl).symm ≪≫
    Scheme.Modules.tensorPullbackCompositionIso (pullback.snd k U.ι) U.ι
      (pullback.fst k U.ι ≫ k) pullback.condition.symm ≪≫
    Functor.isoWhiskerRight (openTensorRestrictionIso U.ι) _

/-- Chain-level comparison obtained by applying the constructed tensor restriction
square degreewise. Source: Stacks Project, Tags 0097 and 0D5U.
(blueprint: def-pc-open-restricted-tensor-complex-iso). -/
def openTensorRestrictionComplexIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    ((Scheme.Modules.restrictFunctor (pullback.fst k U.ι)).mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P) ≅
      ((Scheme.Modules.tensorPullback (pullback.snd k U.ι)).mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatIso.mapHomologicalComplex (openTensorRestrictionSquareIso k U) (.up ℤ)).app P

/-- The localized tensor restriction square, with source the derived open pullback
of the ordinary pullback complex. Both factors are constructed isomorphisms.
Source: Stacks Project, Tags 0D5U and 0D5S.
(blueprint: def-pc-open-restricted-tensor-complex-iso). -/
def openRestrictedTensorDerivedIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (derivedPullback (pullback.fst k U.ι)).obj
        (DerivedCategory.Q.obj
          (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback (pullback.snd k U.ι)).mapHomologicalComplex
          (.up ℤ)).obj
          (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (openRestrictionRepresentativeIso (pullback.fst k U.ι)
    (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
      DerivedCategory.Q.mapIso (openTensorRestrictionComplexIso k U P)

end AlgebraicGeometry.SingleComplexBaseChange
