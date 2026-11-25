/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Boundary points of an affine curve in a compactification

A nonempty affine scheme smooth of positive relative dimension over a field is not proper: being
affine and proper it would be finite, hence discrete, hence of dimension zero. So an open
immersion `i : U ⟶ Z` of such a scheme into a proper scheme has a boundary point: a point of `Z`
outside the range of `i` which is a specialization of a point of `U`
(`AlgebraicGeometry.exists_specializes_notMem_range_of_isProper`).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {U Z : Scheme.{u}}

/-- A nonempty affine scheme smooth of positive relative dimension over a field is not
proper. -/
lemma not_isProper_of_isAffine (f : U ⟶ Spec (.of k)) [IsAffine U] [Nonempty U] (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) f] : ¬ IsProper f := by
  intro hf
  have : IsIntegralHom f :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have : IsFinite f := (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).2
    ⟨inferInstance, inferInstance⟩
  have hd := f.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)
  have : (f.base ⁻¹' {IsLocalRing.closedPoint k}) = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Subsingleton.elim _ _
  rw [this] at hd
  have : DiscreteTopology U := isDiscrete_univ_iff.mp hd
  have h0 := topologicalKrullDim_zero_of_discreteTopology U
  rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n + 1)] at h0
  exact absurd h0 (by norm_cast)

/-- **Boundary points.** Let `i : U ⟶ Z` be an open immersion of a nonempty affine scheme smooth
of positive relative dimension over a field `k` into a proper `k`-scheme `Z`. Then some point of
`Z` outside the range of `i` is a specialization of a point of `U`: otherwise the range of `i`
would be closed, `i` a closed immersion and `U` proper over `k`. -/
lemma exists_specializes_notMem_range_of_isProper (i : U ⟶ Z) [IsOpenImmersion i]
    (aZ : Z ⟶ Spec (.of k)) [IsProper aZ] [IsAffine U] [Nonempty U] (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) (i ≫ aZ)] :
    ∃ (x : U) (z : Z), z ∉ Set.range i.base ∧ i.base x ⤳ z := by
  have := LocallyOfFiniteType.isLocallyNoetherian aZ
  have : CompactSpace Z := (quasiCompact_iff_compactSpace aZ).mp inferInstance
  have : IsNoetherian Z := ⟨⟩
  by_contra! h
  have hcl : IsClosed (Set.range i.base) := by
    refine closure_subset_iff_isClosed.mp fun z hz ↦ ?_
    obtain ⟨_, ⟨x, rfl⟩, hxz⟩ :=
      NoetherianSpace.exists_specializes_of_mem_closure i.isOpenEmbedding.isOpen_range hz
    by_contra hz'
    exact h x z hz' hxz
  have : IsClosedImmersion i := .of_isPreimmersion _ hcl
  exact not_isProper_of_isAffine (i ≫ aZ) n inferInstance

end AlgebraicGeometry
