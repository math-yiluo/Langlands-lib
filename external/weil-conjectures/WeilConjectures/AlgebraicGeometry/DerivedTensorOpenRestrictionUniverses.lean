/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKFlatModel
import WeilConjectures.AlgebraicGeometry.OpenRestrictionTotalTensor

/-! # Derived tensor and exact restriction

Source: Stacks Project, Tag 08DX, proof of (1).
(blueprint: lem-pc-derived-tensor-open-restriction-universes).
-/

@[expose] public section

universe u w wO

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable local instance derivedTensorOpenRestrictionUniversesTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

private theorem tensor_model_iso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P) :
    Nonempty ((DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N
        (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))))) := by
  obtain ⟨e⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const (Discrete PUnit.{1})).obj P)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hP)
  exact ⟨(e.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩⟩

/-- Derived tensor commutes with exact open restriction, allowing independent
localization universes. Source: Stacks Project, Tag 08DX, proof of (1).
Proof: choose K-flat representatives of the first factor. Open restriction is exact,
preserves K-flatness and commutes with the sheaf tensor and the coproducts in
unbounded totalization. The restricted total tensor therefore computes both sides.
The localization comparison transports this calculation between the independently
chosen derived categories. This is natural in both factors, and includes empty opens.
(blueprint: lem-pc-derived-tensor-open-restriction-universes). -/
theorem derivedTensor_openRestriction_iso_universes (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E F : schemeDerivedCategory X) :
    Nonempty
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj (E ⊗ F) ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E ⊗
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj F) := by
  let R :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
  let QX := DerivedCategory.Q
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let QU := DerivedCategory.Q
    (C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
  let RC := R.mapHomologicalComplex (.up ℤ)
  let RD := R.mapDerivedCategory
  let M := QX.objPreimage E
  let N := QX.objPreimage F
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := X.sheaf) M
  have : QuasiIso s := hs
  let eP : QX.obj P ≅ E := asIso (QX.map s) ≪≫ QX.objObjPreimageIso E
  let eN : QX.obj N ≅ F := QX.objObjPreimageIso F
  obtain ⟨a⟩ := tensor_model_iso X P N hP
  obtain ⟨b⟩ := openRestriction_totalTensor_iso X U P N
  obtain ⟨c⟩ := tensor_model_iso U.toScheme (RC.obj P) (RC.obj N)
    (openRestriction_isKFlat X U P hP)
  let dP : RD.obj (QX.obj P) ≅ QU.obj (RC.obj P) :=
    R.mapDerivedCategoryFactors.app P
  let dN : RD.obj (QX.obj N) ≅ QU.obj (RC.obj N) :=
    R.mapDerivedCategoryFactors.app N
  exact ⟨RD.mapIso (tensorIso eP eN).symm ≪≫ RD.mapIso a ≪≫
    R.mapDerivedCategoryFactors.app _ ≪≫ QU.mapIso b ≪≫ c.symm ≪≫
    (tensorIso dP dN).symm ≪≫ tensorIso (RD.mapIso eP) (RD.mapIso eN)⟩

end AlgebraicGeometry
