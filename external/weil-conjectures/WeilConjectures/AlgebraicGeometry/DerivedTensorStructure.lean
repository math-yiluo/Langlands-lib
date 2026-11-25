/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.SchemeModuleFreeYonedaIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Derived tensor structure on O_X-modules

Source: Stacks Project, Cohomology, Tags 06Y7, 06YH and 03EO
(blueprint: def-pc-scheme-derived-tensor-structure).
The tensor is the upstream K-flat derived monoidal construction, specialized to the
shared category of O_X-modules, rather than an arbitrary monoidal structure.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The recorded sheaf tensor structure, specialized to O_X.
Source: Stacks, 06Y7 (blueprint: def-pc-scheme-derived-tensor-structure). -/
noncomputable local instance moduleTensor :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- O_X-modules admit functorial flat resolutions. Source: Stacks, 06Y7
(blueprint: def-pc-scheme-derived-tensor-structure).
Proof: take the sum of extension-by-zero free modules indexed by all local sections
on all opens, with its evaluation epimorphism. These modules are flat on stalks.
Iterate the construction on kernels. Maps of modules act on the section indices,
so this resolution is functorial. -/
theorem schemeModule_hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := by
  let _ := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  apply Abelian.hasFunctorialFlatResolution_of_flat_separator _
    (SheafOfModules.isSeparating_sheafification_freeYoneda
      (moduleRings X.toRingedSpace)).isSeparator_coproduct
  apply ObjectProperty.flat_coproduct
  intro U
  obtain ⟨e⟩ := schemeModule_freeYoneda_iso X U
  apply ObjectProperty.prop_of_iso ObjectProperty.flat e.symm
  have h := SheafOfModules.isFlat_extensionByZero_unit X.sheaf U
  change CategoryTheory.exactFunctor _ _ (MonoidalCategory.tensorRight _) at h
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight
      ((PresheafOfModules.sheafification (𝟙 (moduleRings X.toRingedSpace).obj)).obj
      ((SheafOfModules.extensionByZeroPresheaf (moduleRings X.toRingedSpace) U).obj
        (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U))))) := h.1
  apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
  exact preservesFiniteLimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight _).symm

/-- The K-flat derived tensor monoidal structure on D(O_X): the upstream derived monoidal
structure of the localization `Qh` of the homotopy category, for the recorded sheaf tensor
`SheafOfModules.monoidalCategory X.sheaf` with its symmetry. The additivity and closedness
of that tensor (the first two clauses of `SheafOfModules.tensorClosed`,
lem-pc-sheaf-modules-tensor-closed), the Grothendieck structure and the functorial flat resolutions
(`schemeModule_hasFunctorialFlatResolution`) enter only as propositions used by the
construction; its tensor on objects and morphisms is the K-flat derived tensor.
It is a global instance, so every statement about `schemeDerivedCategory X` uses this one
monoidal structure.
Source: Stacks, 06YH (blueprint: def-pc-scheme-derived-tensor-structure). -/
@[instance_reducible]
noncomputable def schemeDerivedTensorMonoidal
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    MonoidalCategory (schemeDerivedCategory X) := by
  letI := SheafOfModules.symmetricCategory X.sheaf
  haveI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  haveI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  haveI := schemeModule_hasFunctorialFlatResolution X
  haveI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  exact inferInstanceAs (MonoidalCategory
    (DerivedMonoidal (DerivedCategory.Qh
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))))

attribute [instance] schemeDerivedTensorMonoidal

end AlgebraicGeometry
