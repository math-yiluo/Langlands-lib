/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Instances.Discrete
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsGeometry
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsFibrePoint
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsFibreTopology
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsFibreHomeomorphism

/-!
# Points of a zero-dimensional scheme after field extension

Source: Stacks Project, algebra.tex, Lemmas 00KH and 00P4, Theorem 00FV;
Schemes Lemma 01JT (blueprint: lem-weil-pbc-zero-dimensional-base-change-points).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A zero-dimensional finite-type scheme over an algebraically closed field has the
same finite discrete set of points after extension of the ground field.
Source: Stacks Project, algebra.tex, Lemmas 00KH and 00P4, Theorem 00FV;
Schemes Lemma 01JT (blueprint: lem-weil-pbc-zero-dimensional-base-change-points).

The proof first obtains finiteness and discreteness from the Artinian zero-dimensional
case, then identifies each residue field with the algebraically closed base field by
Nullstellensatz.  The point description of a fibre product identifies each fibre of the
projection with `Spec k'`; its unique point gives bijectivity.  Dimension zero and
local Artinianness after field extension make the source of the projection discrete, so
this bijection is a homeomorphism. -/
theorem zeroDimensional_baseChange_points
    (k k' : Type v) [Field k] [Field k'] [IsAlgClosed k] [Algebra k k']
    (C : Scheme.{v}) [C.Over (Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))]
    (hC : topologicalKrullDim C ≤ 0) :
    Finite C ∧ DiscreteTopology C ∧
      (∀ c : C, c ∈ closedPoints C ∧
        IsIso ((C ↘ Spec (.of k)).residueFieldMap c)) ∧
      (∀ c : C, ∃! z : (pullback (C ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{v}),
        (pullback.fst (C ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base z = c) ∧
      topologicalKrullDim
          (pullback (C ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{v}) ≤ 0 ∧
      IsHomeomorph
        (pullback.fst (C ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base := by
  obtain ⟨hfinite, hdiscrete, hclosed⟩ :=
    zeroDimensional_baseChange_geometry k C hC
  exact ⟨hfinite, hdiscrete, hclosed,
    zeroDimensional_baseChange_fibre_points k k' C hC,
    zeroDimensional_baseChange_fibre_topology k k' C hC,
    zeroDimensional_baseChange_fibre_homeomorphism k k' C hC⟩

end AlgebraicGeometry
