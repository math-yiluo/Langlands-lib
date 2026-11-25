/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.CoherentKernelConditionGluing

/-! # Descent of finite type for a kernel on an open cover

Source: Stacks Project, Modules, Definitions 01BV, 01B5 and Section 01AF.
(blueprint: lem-weil-pbc-coherent-kernel-condition-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A single kernel on an open `W` is finite type if the finite-type kernel condition
holds for the restrictions of the target module to the members of an open cover.
No finite-type hypothesis on the target module is required.
Source: Stacks Project, Modules, Definitions 01BV (definition-coherent), 01B5
(definition-finite-type), and Section 01AF (section-kernels).
(blueprint: lem-weil-pbc-coherent-kernel-condition-descent).

Proof: Intersect `W` with each member `U i` of the cover. These intersections cover
`W`, including when the index type is empty and `X` is empty. On each intersection,
restrict the map `f`. Restriction preserves the structure module and finite direct
sums, so its source identifies with the free module of rank `n`. Transitivity of
restriction identifies its target with the restriction of `F|_(U i)` to that
intersection. The local hypothesis therefore makes the kernel of this map finite
type. Kernels are computed sectionwise, so restriction of `kernel f` is isomorphic
to this kernel; finite type is invariant under isomorphism. For any point of `W`,
choose a cover member containing it, then the neighbourhood with finite generators
for this local kernel. This neighbourhood is open in `W` and generates the original
kernel there by transitivity of restriction. Hence `kernel f` is of finite type.
There is no surjectivity requirement on `f`, and rank zero is included. -/
theorem coherent_kernel_condition_descent (X : Scheme.{u}) (F : X.Modules)
    (I : Type u) (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hK : ∀ (i : I) (V : (U i).toScheme.Opens) (n : ℕ)
      (f : SheafOfModules.free (R := (U i).toScheme.ringCatSheaf.over V)
        (ULift.{u} (Fin n)) ⟶ ((Scheme.Modules.restrictFunctor (U i).ι).obj F).over V),
      (kernel f).IsFiniteType)
    (W : X.Opens) (n : ℕ)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over W) (ULift.{u} (Fin n)) ⟶
      F.over W) : (kernel f).IsFiniteType := by
  obtain ⟨σ, hσ⟩ := coherent_kernel_condition_local_generators X F I U hU hK W n f
  apply SheafOfModules.IsFiniteType.mk
  show ∃ τ : SheafOfModules.LocalGeneratorsData.{u} (kernel f), τ.IsFiniteType
  exact ⟨σ, hσ⟩

end AlgebraicGeometry
