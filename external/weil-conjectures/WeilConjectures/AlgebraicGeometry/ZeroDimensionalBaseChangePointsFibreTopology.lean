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
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsGeometry

/-! Intermediate fibre facts for zero-dimensional base change.
Source: Stacks Project, schemes.tex Lemma 01JT and algebra.tex Lemma 00P4.
(blueprint: new-zdbp-fibres-topology)
-/

set_option linter.style.haveILetI false

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The base-changed scheme is zero-dimensional and discrete. Source: Stacks Project,
algebra.tex Lemma 00P4. Base change preserves local quasi-finiteness and local
Artinianness; the Artinian criterion gives discreteness and dimension at most zero.
(blueprint: new-zdbp-fibres-topology) -/
theorem zeroDimensional_baseChange_fibre_topology
    (k k' : Type v) [Field k] [Field k'] [IsAlgClosed k] [Algebra k k']
    (C : Scheme.{v}) [C.Over (Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))]
    (hC : topologicalKrullDim C ≤ 0) :
    topologicalKrullDim
      (pullback (C ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{v}) ≤ 0 := by
  let f : C ⟶ Spec (.of k) := C ↘ Spec (.of k)
  let g := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  letI : DiscreteTopology C := (zeroDimensional_baseChange_geometry k C hC).2.1
  letI : LocallyQuasiFinite f :=
    locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
      (fun _ ↦ IsDiscrete.univ.mono (Set.subset_univ _))
  letI : IsLocallyArtinian (pullback f g) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd f g)
  exact topologicalKrullDim_zero_of_discreteTopology _

end AlgebraicGeometry
