/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.CoherentIteratedSliceRelations
import WeilConjectures.AlgebraicGeometry.FiniteTypeKernelLocalGenerators

/-! # Finite type kernels into a coherent module on an open slice

Source: Stacks Project, Modules, Lemma 01BY (2), with Definition 01BV.
(blueprint: lem-weil-pbc-coherent-finite-type-kernel-over).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- A map from a finite type module on an open slice to the restriction of a coherent
module has a finite type kernel.
Source: Stacks Project, Modules, Lemma 01BY (2), with Definition 01BV.
(blueprint: lem-weil-pbc-coherent-finite-type-kernel-over).

Proof: Opens of the slice over U are exactly the opens of X contained in U. Restrict
local finite generating families for G to these opens. The relation condition for G
applies to every such open, so G restricted to U is coherent. For each point of U,
choose a finite free epimorphism onto F on a neighborhood. The kernel L of its
composite into G is finite type by the relation condition. Each section of the
kernel of φ lifts locally through this epimorphism, and its lift lies in L. Thus L
maps epimorphically onto the kernel of φ. Images of finite type modules are finite
type, so these local kernels are finite type; the neighborhoods cover U. This is
the local free relations and image argument of Lemma 01BY (2) on the slice, with no
assumption on the behavior of F at the boundary of U. -/
theorem coherent_finiteType_kernel_over (X : RingedSpace.{u})
    (U : Opens X) (G : SheafOfModules.{u} (moduleRings X))
    (F : SheafOfModules.{u} ((moduleRings X).over U))
    (φ : F ⟶ G.over U) (hF : F.IsFiniteType) (hG : IsCoherent X G) :
    (kernel φ).IsFiniteType := by
  obtain ⟨q, hq⟩ := hF.exists_localGeneratorsData
  apply finiteType_kernel_local_generators X U φ q
  intro i
  have : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact coherent_iterated_slice_relations X U G hG (q.X i)
    (q.generators i).I ((q.generators i).π ≫ φ.over (q.X i))

end AlgebraicGeometry.RingedSpace
