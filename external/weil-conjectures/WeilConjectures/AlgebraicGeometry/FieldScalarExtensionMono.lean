/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldScalarExtension
public import Mathlib.CategoryTheory.Functor.EpiMono
import WeilConjectures.AlgebraicGeometry.FieldScalarPresheafPullbackMono

/-! # Scalar extension preserves monomorphisms

Source: Stacks Project, Modules, Tag 02N4.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

private theorem constantModules_preservesMonomorphisms
    {k : Type u} [Ring k] (X : TopCat.{u}) :
    (modulePresheafToConstantModules.{u, v} (k := k) X).PreservesMonomorphisms where
  preserves {V W} f _ := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact (ModuleCat.mono_iff_injective (f.app U)).mp inferInstance

/-- Scalar extension preserves monomorphisms over a field.

Source: Stacks Project, Modules, Tag 02N4.
(blueprint: lem-sc-field-scalar-extension-mono).

Proof: the inclusion of sheaves into presheaves preserves monomorphisms, the
conversion to modules over the constant ring presheaf preserves pointwise
injections, and extension of scalars from a field preserves monomorphisms
before sheafification. Module sheafification preserves finite limits and hence
monomorphisms. Compose these four preservation statements. -/
theorem fieldScalarExtension_preservesMonomorphisms
    {k : Type u} [Field k] (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (α : k →+* R.obj.obj (op ⊤)) :
    (fieldScalarExtension.{u, v} X R α).PreservesMonomorphisms := by
  have := constantModules_preservesMonomorphisms.{u, v} (k := k) X
  have := fieldScalarPresheafPullback_preservesMonomorphisms.{u, v} X R α
  let := fieldScalarPresheafPullback_isRightAdjoint.{u, v} X R α
  let := fieldScalarExtension_hasSheafify.{u, v} X
  let := fieldScalarExtension_wEqualsLocallyBijective.{u, v} X
  unfold fieldScalarExtension
  infer_instance

end SheafOfModules
