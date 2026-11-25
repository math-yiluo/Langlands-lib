/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension
import WeilConjectures.AlgebraicGeometry.ArtinianLiftingFromEtaleInfinitesimal
import WeilConjectures.AlgebraicGeometry.SmoothArtinianLiftingAtPoint
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.Topology.KrullDimension
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-! Pointwise étale neighbourhood extracted from infinitesimal étaleness.

The proof follows the pointwise part of Stacks Lemma 0A43: the Artinian lifting
criterion gives smoothness, the zeroth neighbourhood gives fibre dimension zero,
and shrinking yields an étale neighbourhood. (blueprint: lem-weil-pbc-etale-infinitesimal-pointwise)
-/
private theorem fibre_dimension_zero_of_etale_closed_baseChange
    {X S Z : Scheme.{u}} (g : X ⟶ S) (i : Z ⟶ S) [IsClosedImmersion i]
    [Etale (pullback.snd g i)] (x : X)
    (hx : g x ∈ Set.range i) : topologicalKrullDimAt (g.asFiber x) = 0 := by
  let r := S.fromSpecResidueField (g x)
  have hker : i.ker ≤ r.ker := by
    rw [Scheme.IdealSheafData.le_ker_iff_range_subset_support]
    rw [Scheme.range_fromSpecResidueField]
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
    exact Set.singleton_subset_iff.mpr hx
  let k := IsClosedImmersion.lift i r hker
  have hk : k ≫ i = r := IsClosedImmersion.lift_fac i r hker
  have : Etale (pullback.snd g r) := by
    rw [← hk]
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd g i k]
    infer_instance
  have : DiscreteTopology (g.fiber (g x)) := by
    change DiscreteTopology (pullback g r : Scheme.{u})
    let q := pullback.snd g r
    have : DiscreteTopology (q ⁻¹' {q (g.asFiber x)}) :=
      (q.isDiscrete_preimage_singleton _).to_subtype
    have heq : q ⁻¹' {q (g.asFiber x)} = Set.univ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [heq] at this
    exact (Homeomorph.Set.univ (g.fiber (g x))).discreteTopology
  apply topologicalKrullDimAt_eq_of_forall (x := g.asFiber x)
  intro U hU
  refine le_antisymm ?_ ?_
  · exact (topologicalKrullDim_subspace_le (g.fiber (g x)) U).trans
      (topologicalKrullDim_zero_of_discreteTopology (g.fiber (g x)))
  · exact Order.krullDim_nonneg_iff.mpr
      ⟨⟨closure {(⟨g.asFiber x, hU⟩ : U)}, isIrreducible_singleton.closure,
        isClosed_closure⟩⟩

/-- Every point over the closed subscheme has an etale neighbourhood. The proof uses
smoothness from the Artinian lifting criterion, zero fibre dimension from the etale
zeroth neighbourhood, and the etale shrinking lemma.
(blueprint: lem-weil-pbc-etale-infinitesimal-pointwise) -/
theorem etale_infinitesimal_pointwise
    {X S Z : Scheme.{u}} (g : X ⟶ S) (i : Z ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsClosedImmersion i] (J : S.IdealSheafData) (hJ : J = i.ker)
    (h_etale : ∀ n : ℕ,
      Etale (pullback.snd g ((J ^ (n + 1)).subschemeι)))
    (x : X) (hx : (g : X → S) x ∈ Set.range (i : Z → S)) :
    ∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ g) := by
  obtain ⟨U, hxU, hSmooth⟩ :=
    (smooth_near_iff_artinian_lifting_at_point g x).mpr
      (artinian_lifting_tests_of_etale_infinitesimal g i J hJ h_etale x hx)
  have : Etale (pullback.snd g J.subschemeι) := by
    have h₀ := h_etale 0
    change Etale (pullback.snd g ((J ^ 1).subschemeι)) at h₀
    rw [pow_one] at h₀
    exact h₀
  have hxJ : g x ∈ Set.range J.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, hJ, Scheme.Hom.support_ker,
      i.isClosedEmbedding.isClosed_range.closure_eq]
    exact hx
  have hDim := fibre_dimension_zero_of_etale_closed_baseChange g J.subschemeι x hxJ
  obtain ⟨W, hWU, hxW, hEtale⟩ :=
    exists_etale_open_of_smooth_of_fibre_dimension_zero g x U hxU hSmooth hDim
  exact ⟨W, hxW, hEtale⟩
end AlgebraicGeometry
