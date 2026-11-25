/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.DerivedTensorUnitCompact
public import Mathlib.AlgebraicGeometry.Noetherian
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option linter.unusedVariables false in
/-- The quasi-coherent direct-image, unit, and tensor data for a proper noetherian morphism.
Sources: Stacks Project, Tags 08D5, 08DW, 08DX and 09M1.
Proof: properness supplies quasi-compactness and quasi-separatedness, so derived direct
image preserves quasi-coherent cohomology. Transport quasi-coherence along the existing
tensor-unit isomorphism. Derived pullback preserves quasi-coherent cohomology, and
canonical derived tensor preserves it; apply these successively to K and E.
(blueprint: lem-sc-smooth-proper-qcoh-data). -/
theorem smoothProper_qcoh_data
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((moduleRings Y.toRingedSpace).over U))]
    : ∃ (hRf : ∀ E : schemeDerivedQCohCategory X,
        schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
      (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
      (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory X),
        schemeDerivedQCohProperty X (((derivedPullback f).obj K.obj) ⊗ E.obj)),
      ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory X),
        schemeDerivedQCohProperty X (((derivedPullback f).obj K.obj) ⊗ E.obj) := by
  classical
  have hRf : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj) :=
    fun E ↦ schemeDerivedDirectImage_preserves_QCoh f E.obj E.property
  obtain ⟨U, ⟨e⟩, _⟩ := exists_compact_derivedTensorUnit Y
  have hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)) := by
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (U.property n)
  have hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory X),
      schemeDerivedQCohProperty X (((derivedPullback f).obj K.obj) ⊗ E.obj) := by
    intro K E
    exact canonical_derivedTensor_preserve_QCoh X _ _
      ((derivedPullback_tensor_preserve_QCoh f).1 K.obj K.property) E.property
  exact ⟨hRf, hO, hTensor, hTensor⟩
end AlgebraicGeometry
