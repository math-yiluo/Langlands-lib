/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Instances.Discrete
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! Intermediate geometric facts for zero-dimensional base change.
Source: Stacks Project, algebra.tex, Lemmas 00KH and 00FV.
(blueprint: new-zdbp-geometry)
-/

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A zero-dimensional finite-type scheme over an algebraically closed field is finite and
 discrete, and its structure morphism induces residue-field isomorphisms. Source: Stacks
 Project, algebra.tex, Lemma 00KH and Theorem 00FV. Finite type over a field makes C locally
 Noetherian. The dimension bound makes its affine rings Artinian, hence C is discrete.
 Quasi-compactness then makes its point set finite. Every singleton is closed. Nullstellensatz
 makes each closed-point residue field a finite extension of k; algebraic closedness makes the
 induced field map an isomorphism. The empty scheme has a finite discrete space and the pointwise
 claims are vacuous. (blueprint: new-zdbp-geometry) -/
theorem zeroDimensional_baseChange_geometry
    (k : Type v) [Field k] [IsAlgClosed k]
    (C : Scheme.{v}) [C.Over (Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))]
    (hC : topologicalKrullDim C ≤ 0) :
    Finite C ∧ DiscreteTopology C ∧
      (∀ c : C, c ∈ closedPoints C ∧
        IsIso ((C ↘ Spec (.of k)).residueFieldMap c)) := by
  let f : C ⟶ Spec (.of k) := C ↘ Spec (.of k)
  letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsLocallyArtinian C := IsLocallyArtinian.of_topologicalKrullDim_le_zero hC
  letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsArtinianScheme C := ⟨⟩
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro c
  have hc : IsClosed ({c} : Set C) := isClosed_discrete _
  refine ⟨by simpa [closedPoints] using hc, ?_⟩
  have hbase : IsIso ((Spec (.of k)).fromSpecResidueField (f c)) := by
    have he := SpecMap_residueFieldIsoBase_inv (𝟙 (Spec (.of k))) (f c)
      (isClosed_discrete _)
    simp only [Category.comp_id] at he
    rw [← he]
    infer_instance
  have hcomp : IsIso (Spec.map (f.residueFieldMap c) ≫
      (Spec (.of k)).fromSpecResidueField (f c)) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← SpecMap_residueFieldIsoBase_inv f c hc]
    infer_instance
  have hmap : IsIso (Spec.map (f.residueFieldMap c)) :=
    (isIso_comp_right_iff _ _).mp hcomp
  letI : IsIso (Scheme.Spec.map (f.residueFieldMap c).op) := hmap
  have hop : IsIso (f.residueFieldMap c).op :=
    isIso_of_reflects_iso (f.residueFieldMap c).op Scheme.Spec
  exact isIso_of_op _

end AlgebraicGeometry
