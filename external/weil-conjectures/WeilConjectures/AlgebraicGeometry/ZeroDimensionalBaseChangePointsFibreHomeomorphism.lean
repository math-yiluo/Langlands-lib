/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Instances.Discrete
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Artinian
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsGeometry
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsFibrePoint
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsFibreTopology

/-! Intermediate fibre facts for zero-dimensional base change.
Source: Stacks Project, schemes.tex Lemma 01JT and algebra.tex Lemma 00P4.
(blueprint: new-zdbp-fibres-homeomorphism)
-/

set_option linter.style.haveILetI false

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The projection after base change is a homeomorphism. Source: topology of discrete
spaces and the preceding point and dimension results. A continuous bijection between
discrete spaces has continuous inverse. (blueprint: new-zdbp-fibres-homeomorphism) -/
theorem zeroDimensional_baseChange_fibre_homeomorphism
    (k k' : Type v) [Field k] [Field k'] [IsAlgClosed k] [Algebra k k']
    (C : Scheme.{v}) [C.Over (Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))]
    (hC : topologicalKrullDim C ≤ 0) :
    IsHomeomorph
      (pullback.fst (C ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k k')) )).base := by
  let f : C ⟶ Spec (.of k) := C ↘ Spec (.of k)
  let g := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  letI : DiscreteTopology C := (zeroDimensional_baseChange_geometry k C hC).2.1
  letI : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
  letI : IsLocallyArtinian (pullback f g) :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero
      (zeroDimensional_baseChange_fibre_topology k k' C hC)
  have hpoints := zeroDimensional_baseChange_fibre_points k k' C hC
  refine ⟨(pullback.fst f g).continuous, ?_, ?_, ?_⟩
  · exact fun _ _ ↦ isOpen_discrete _
  · intro x y hxy
    obtain ⟨z, hz, hu⟩ := hpoints ((pullback.fst f g) x)
    exact (hu x rfl).trans (hu y hxy.symm).symm
  · intro c
    obtain ⟨z, hz, _⟩ := hpoints c
    exact ⟨z, hz⟩

end AlgebraicGeometry
