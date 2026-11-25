/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.AlgebraicGeometry.FieldScalarExtensionAdjunction
import WeilConjectures.AlgebraicGeometry.FieldScalarExtensionMono

/-! # Restricting module sheaves to a field preserves injectives

Source: Stacks Project, Cohomology, Tag 02N5; Modules, Tag 02N4;
Homology, Tag 015Z.
(blueprint: lem-sc-field-scalar-restriction-injectives).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

/-- Field restriction of module sheaves preserves injective objects.

Source: Stacks Project, Cohomology, Tag 02N5; Modules, Tag 02N4;
Homology, Tag 015Z.
(blueprint: lem-sc-field-scalar-restriction-injectives).

Proof: construct the map from the constant ring presheaf k to R by restricting α
from the terminal open. Regard vector-valued presheaves as modules over that
constant presheaf. Presheaf pullback followed by module sheafification gives a
left adjoint to the displayed scalar-restriction functor. The hom bijection and
its naturality are proved by composing the presheaf-pullback and sheafification
adjunctions. The inclusion of sheaves into presheaves preserves monomorphisms;
so do conversion to constant-ring modules, presheaf scalar extension over a field,
and module sheafification. Thus the left adjoint preserves monomorphisms, and
Mathlib's adjunction criterion proves that the right adjoint preserves injectives.
The presheaf tensor uses R(U) as a right k-module by r · c = r α_U(c), so neither
commutativity of R nor centrality of α is assumed. The construction and argument
work in every module universe admitted by the original statement, and include
the empty space and the zero ring sheaf. No stalk or Ext comparison is used. -/
theorem fieldScalarRestriction_preservesInjectives
    {k : Type u} [Field k] (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (α : k →+* R.obj.obj (op ⊤)) :
    Functor.PreservesInjectiveObjects
      (forgetToSheafModuleCat.{u} R (op ⊤) isTerminalTop.op ⋙
        sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars α)) := by
  have := fieldScalarExtension_preservesMonomorphisms X R α
  obtain ⟨adj⟩ := nonempty_fieldScalarExtensionAdjunction X R α
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

end SheafOfModules
