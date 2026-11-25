/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePoints
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Geometric data for a zero-dimensional base change, independently of any sheaf.
Source: Stacks Project, Tags 00KH, 00FV and 01JT; the point description in
lem-weil-pbc-zero-dimensional-base-change-points.
(blueprint: lem-weil-pbc-zero-dimensional-base-change-geometric-points).

Proof: Nullstellensatz identifies every residue field of C with k. The local
Artinian pieces remain local Artinian after extending to k', with residue field k'.
Thus projection induces a bijection on points, and C' has dimension at most zero.
Finite type and separatedness are stable under base change, giving IsCurve f'.
At each point of C', the canonical residue-field morphism Spec k' → C' gives the
chosen geometric point. For the empty scheme the equivalence and family are empty.
An arbitrary cartesian square is isomorphic to the canonical fibre product, so
transport these constructions across that isomorphism. -/
theorem zeroDimensional_baseChange_geometric_points {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] (hC : topologicalKrullDim C ≤ 0)
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) :
    IsCurve f' ∧ topologicalKrullDim C' ≤ 0 ∧
      ∃ b : C' ≃ C, (∀ c', b c' = ι' c') ∧
        ∃ s : C' → (Spec (.of k') ⟶ C'), ∀ c', s c' default = c' := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let φ : k →+* k' := (Spec.preimage ι).hom
  let : Algebra k k' := φ.toAlgebra
  have hi : Spec.map (CommRingCat.ofHom (algebraMap k k')) = ι := by
    exact Spec.map_preimage ι
  let : IsSeparated (C ↘ Spec (.of k)) := inferInstanceAs (IsSeparated f)
  let : LocallyOfFiniteType (C ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType f)
  let : QuasiCompact (C ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact f)
  obtain ⟨_, hdiscrete, _, _, hd, hp⟩ := zeroDimensional_baseChange_points k k' C hC
  rw [hi] at hd hp
  let e := h.isoPullback
  have he : e.hom ≫ CategoryTheory.Limits.pullback.fst f ι = ι' := h.isoPullback_hom_fst
  have hdim : topologicalKrullDim C' ≤ 0 := by
    rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
    exact hd
  let : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
  let : LocallyOfFiniteType f' := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact f' := MorphismProperty.of_isPullback h inferInstance
  refine ⟨⟨hdim.trans (by norm_num)⟩, hdim, ?_⟩
  let b := e.hom.homeomorph.toEquiv.trans (hp.homeomorph _).toEquiv
  refine ⟨b, ?_, ?_⟩
  · intro c'
    change (CategoryTheory.Limits.pullback.fst f ι) (e.hom c') = ι' c'
    exact congrArg (fun g : C' ⟶ C ↦ g c') he
  · let : DiscreteTopology C := hdiscrete
    let eb := e.hom.homeomorph.trans (hp.homeomorph _)
    let : DiscreteTopology C' := eb.isEmbedding.discreteTopology
    refine ⟨fun c' ↦ pointOfClosedPoint f' c' (isClosed_discrete _), ?_⟩
    intro c'
    exact pointOfClosedPoint_apply _ _ _ _

end AlgebraicGeometry
