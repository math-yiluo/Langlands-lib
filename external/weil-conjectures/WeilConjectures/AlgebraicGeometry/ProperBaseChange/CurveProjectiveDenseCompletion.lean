/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.Curve.DimOneQuasiProjective
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dense projective completion of a scheme of dimension at most one

## References

* Stacks Project, Varieties, Tag 0BXV
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated finite type scheme of dimension at most one over a field admits an
H-projective completion with dense, scheme-theoretically dense open image and finite
boundary of closed points. The completion is reduced when the source is reduced and
empty when the source is empty. -/
theorem exists_projective_dense_completion_of_dim_le_one
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (C : Scheme.{u}) (g : C ⟶ Spec (.of k)) (a : X ⟶ C),
      IsHProjective g ∧ topologicalKrullDim C ≤ 1 ∧ IsOpenImmersion a ∧
      a ≫ g = X ↘ Spec (.of k) ∧ DenseRange a ∧
      (∀ U : C.Opens, Function.Injective (a.app U)) ∧
      (Set.range a)ᶜ.Finite ∧ (∀ c : C, c ∉ Set.range a → IsClosed ({c} : Set C)) ∧
      (IsReduced X → IsReduced C) ∧ (IsEmpty X → IsEmpty C) := by
  obtain ⟨N, U, gU, i, j, hi, hj, hig, hjg⟩ :=
    exists_closed_open_immersion_projectiveSpace_of_dim_le_one
      (X ↘ Spec (.of k)) (by simpa only [X.dim_eq_topologicalKrullDim] using hdim)
  let := hi
  let := hj
  let h := i ≫ j
  have : IsImmersion h := inferInstance
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : QuasiCompact h := inferInstance
  let C := h.image
  let g : C ⟶ Spec (.of k) :=
    h.imageι ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)
  let a : X ⟶ C := h.toImage
  have : IsHProjective g := ⟨⟨ULift.{u} (Fin (N + 1)), inferInstance,
    h.imageι, inferInstance, rfl⟩⟩
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian C := ⟨⟩
  have hdense : DenseRange a := a.denseRange
  have hCdim : topologicalKrullDim C ≤ 1 := by
    refine (topologicalKrullDim_le_of_dense g a.opensRange hdense).trans ?_
    change topologicalKrullDim (Set.range a) ≤ 1
    rw [← a.isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range]
    exact hdim
  have hboundary : (Set.range a)ᶜ.Finite ∧
      ∀ c : C, c ∉ Set.range a → IsClosed ({c} : Set C) := by
    have hc : IsClosed (Set.range a)ᶜ := a.isOpenEmbedding.isOpen_range.isClosed_compl
    have hgen : ∀ c ∈ (Set.range a)ᶜ,
        ∃ η ∈ (Set.univ : Set C), η ⤳ c ∧ η ∉ (Set.range a)ᶜ := by
      intro c _
      obtain ⟨η, _, hη, hηc⟩ :=
        isClosed_univ.exists_maximal_specializes (Set.mem_univ c)
      have hηa : η ∈ Set.range a :=
        mem_of_dense_of_forall_specializes_eq a.isOpenEmbedding.isOpen_range hdense
          (fun y hy ↦ hη y (Set.mem_univ y) hy)
      exact ⟨η, Set.mem_univ _, hηc, not_not.mpr hηa⟩
    have hdrop : topologicalKrullDim ↥((Set.range a)ᶜ) < (1 : ℕ) :=
      topologicalKrullDim_lt_of_forall_exists_specializes isClosed_univ hc
        (Set.subset_univ _) hgen (d := 1)
        (lt_of_le_of_lt ((topologicalKrullDim_subspace_le C Set.univ).trans hCdim)
          (by decide))
    exact hc.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero
      (ENat.WithBot.lt_add_one_iff.mp (by simpa using hdrop))
  refine ⟨C, g, a, inferInstance, hCdim, inferInstance, ?_, hdense,
    a.app_injective, hboundary.1, hboundary.2, ?_, ?_⟩
  · dsimp only [a, g]
    rw [h.toImage_imageι_assoc]
    dsimp only [h]
    rw [Category.assoc, hjg, hig]
  · intro hX
    let := hX
    exact IsSchemeTheoreticallyDominant.isReduced a
  · intro hX
    let := hX
    refine ⟨fun c ↦ ?_⟩
    have hc : c ∈ closure (Set.range a) := hdense c
    simp only [Set.range_eq_empty, closure_empty, Set.mem_empty_iff_false] at hc

end AlgebraicGeometry
