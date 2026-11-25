/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
public import WeilConjectures.Algebra.Homology.ScalarInternalHomData
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower

/-! # Closed slice comparison with transported pro-etale coefficients

Comparison data and their defining section and representative equations
(auxiliary; not a blueprint node).

Source: Hemo--Richarz--Scholbach, Lemma 4.5, and Stacks Project, Tags 03CE,
03EL, 07A4, 08J7, 08J9, 08JB and 0FPT
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.Scheme

/-- Slice coefficients, written on the equivalent small site of the source scheme.
Source: Stacks 03CE (auxiliary; not a blueprint node). -/
abbrev proEtaleSliceRing {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
    U.hom U.prop).obj O

/-- Exact sectionwise module restriction, under the canonical equivalence with the slice.
Source: Stacks 03CE, 08JB
(auxiliary; not a blueprint node). -/
def proEtaleSliceModuleRestriction {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    proEtaleRingModules X O ⥤ proEtaleRingModules U.left (proEtaleSliceRing U O) :=
  letI := ProEt.isContinuous_overMap (V := U.left) (U := X) U.prop
  SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop)
    (J := ProEt.topology U.left) (K := ProEt.topology X) (𝟙 _)

/-- The coefficient isomorphism b = c after the inverse of the canonical delta.
Source: HRS Lemma 4.5 and Stacks 03CE
(auxiliary; not a blueprint node). -/
def proEtaleSliceCoefficientIso {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
    (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1}) :
    proEtaleSliceRing U O ≅ B :=
  (delta.sheafIso.app O).symm ≪≫ c

/-- Termwise scalar transport: underlying abelian sheaves and maps are unchanged,
and the B-action is restriction along b inverse.
Source: Stacks 03CZ, 03CY
(auxiliary; not a blueprint node). -/
abbrev proEtaleSliceScalarTransport {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (b : proEtaleSliceRing U O ≅ B) :=
  SheafOfModules.scalarRestriction.{u + 1, u, u + 1} b.inv

/-- The fixed ordinary derived internal Hom on arbitrary pro-etale coefficients.
Source: Stacks 08J7 (auxiliary; not a blueprint node). -/
abbrev proEtaleCoefficientHom (X : Scheme.{u})
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  derivedInternalHomOfUniverses.{u + 1, u, u + 1} (ProEt.topology X) O

/-- The distinguished inverse-image section, followed by extension of scalars.
Source: Stacks 03CE, 03D2, 03EL
(auxiliary; not a blueprint node). -/
def proEtaleSlicePullbackSection {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
    (N : proEtaleRingModules X O) (V : U.left.ProEt)
    (m : N.val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))) :
    ((proEtaleRingModulePullback U.hom O B c).obj N).val.obj (op V) :=
  ((proEtaleRingModulePullback U.hom O B c).obj N).val.map
    (proEtaleObjectInverseImageIndexPoint U V).hom.op
      (((proEtaleRingModuleAdjunction U.hom O B c).unit.app N).val.app _ m)

attribute [local irreducible] CoefficientTensorModels.iso

namespace ProEtaleCoefficientSliceComparison

variable {X : Scheme.{u}} (U : X.ProEt)
  (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
  (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1})

/-- The fixed scalar isomorphism b = c delta inverse, without a new coefficient choice.
Source: Stacks 03CE (auxiliary; not a blueprint node). -/
abbrev b := proEtaleSliceCoefficientIso U O B c delta

/-- Scalar transport along b inverse, acting identically on underlying abelian sheaves.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
abbrev e := proEtaleSliceScalarTransport U O B (b U O B c delta)

/-- Actual exact module inverse image with the specified coefficient isomorphism c.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
abbrev f := proEtaleRingModulePullback U.hom O B c

variable (S : CoefficientClosedStructure (proEtaleCoefficientHom X O))
  (SR : CoefficientClosedStructure (proEtaleCoefficientHom U.left (proEtaleSliceRing U O)))
  (SB : CoefficientClosedStructure (proEtaleCoefficientHom U.left B))
  (T : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) O S)
  (TR : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left)
    (proEtaleSliceRing U O) SR)
  (TB : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left) B SB)

end ProEtaleCoefficientSliceComparison

end AlgebraicGeometry.Scheme
