/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupResolutionData
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.GlobalTensorPullbackMatesIsIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Realizing a resolution pairing in the derived category

Source: Stacks Project, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-resolution-realization)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

@[instance_reducible] local instance cupRealizationMonoidalCategory :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
@[instance_reducible] local instance cupRealizationSymmetricCategory :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf
attribute [local instance] globalPullbackMatesColimits
local instance cupRealizationMonoidalPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
@[instance_reducible] local instance cupRealizationMonoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance cupRealizationHasFunctorialFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
local instance cupRealizationIsGrothendieckAbelian : IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)

local instance cupRealizationDerivedMonoidal :
    Functor.HasDerivedMonoidalCategory
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

@[instance_reducible] local instance cupRealizationQLax :
    Functor.LaxMonoidal
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
  inferInstance

/-- Extend a nonnegative resolution to integer degrees by zero.
Source: Stacks Project, Tag 0FKU.
(blueprint: def-sc-module-cup-realization-complex-data) -/
abbrev CupAcyclicResolution.integerComplex {F : X.Modules} (D : CupAcyclicResolution F) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  D.K.extend ComplexShape.embeddingUpNat

/-- The localized augmentation, with the extended single complex identified with F[0].
(blueprint: def-sc-module-cup-realization-complex-data)
-/
def CupAcyclicResolution.derivedAugmentation {F : X.Modules} (D : CupAcyclicResolution F) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⟶
      DerivedCategory.Q.obj D.integerComplex :=
  DerivedCategory.Q.map
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
      HomologicalComplex.extendMap D.augmentation ComplexShape.embeddingUpNat)

/-- An augmentation is inverted by the derived localization.
(blueprint: def-sc-module-cup-realization-complex-data)
-/
instance CupAcyclicResolution.derivedAugmentation_isIso
    {F : X.Modules} (D : CupAcyclicResolution F) : IsIso D.derivedAugmentation := by
  let : QuasiIso D.augmentation := D.quasiIso
  unfold CupAcyclicResolution.derivedAugmentation
  rw [Functor.map_comp]
  infer_instance

/-- The section formula for the cochain morphism realizing the bilinear pairing.
It specifies all nonzero tensor summands; extension by zero supplies the others.
(blueprint: def-sc-module-cup-realization-complex-data)
-/
def CupResolutionPairing.Realizes {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex) : Prop :=
  ∀ (p q : ℕ) (V : X.Opens) (a : Γ(D.left.K.X p, V)) (b : Γ(D.right.K.X q, V)),
    ((HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
        (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by omega) ≫ t.f (p + q) ≫
      (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom).val.app (op V)
        (tmulSection
          ((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) a)
          ((D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) b)))
      = D.pair p q V a b

/-- The derived morphism attached to a cochain realization. This is an explicit
composite of localized augmentations and the canonical tensor comparison.
(blueprint: def-sc-module-cup-realization-complex-data)
-/
def CupResolutionPairing.derivedMap {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⊗
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj (F ⊗ G)) :=
  (D.left.derivedAugmentation ⊗ₘ D.right.derivedAugmentation) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q D.left.integerComplex D.right.integerComplex ≫
    DerivedCategory.Q.map t ≫ inv D.target.derivedAugmentation


end
end AlgebraicGeometry.Scheme.Modules
