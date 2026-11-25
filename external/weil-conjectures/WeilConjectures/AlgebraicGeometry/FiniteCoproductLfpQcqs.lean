/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Quasi-compactness, quasi-separatedness and local finite presentation of finite coproducts

Source: Stacks Project, Tags 01KO and 01TQ, applied to the disjoint open summands of a
coproduct of schemes (blueprint: lem-weil-pbc-finite-coproduct-lfp-qcqs).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite coproduct of schemes preserves quasi-compactness and quasi-separatedness, and
its induced morphism is locally of finite presentation when each component morphism is.
Source: Stacks Project, Tags 01KO and 01TQ
(blueprint: lem-weil-pbc-finite-coproduct-lfp-qcqs).

Proof:
1. By [lem-weil-pbc-scheme-coproduct-family], the coprojections identify the summands with
   pairwise disjoint open-and-closed subschemes covering the coproduct. If every summand is
   quasi-compact, each image is compact. Their finite union is compact: restrict an open
   cover to each summand, take a finite subcover there, and unite these finite choices.
2. For quasi-separatedness, take all affine opens in each summand. Their images form an
   affine open cover of the coproduct. Two such opens in distinct summands have empty
   intersection. Within one summand their intersection is quasi-compact by
   [lem-weil-pbc-quasi-separated-affine-cover-criterion], part (1). Part (2) of that criterion
   (Stacks Tag 01KO) then gives quasi-separatedness of the coproduct.
3. For local finite presentation, a point lies in one open summand. Choose affine
   neighbourhoods in that summand and in the target on which the component ring map is
   finitely presented, by [def-sbc-locally-finite-presentation]. The open immersion transfers
   the source neighbourhood to the coproduct. The induced ring map is isomorphic to the
   component ring map because `Sigma.ι V a ≫ Sigma.desc g = g a`. The pointwise definition,
   equivalently source locality in Stacks Tag 01TQ, gives the conclusion.
For an empty index type, the coproduct is the empty scheme: compactness holds, the empty
cover satisfies the affine-intersection criterion, and there are no points to check. -/
theorem finite_coproduct_lfp_qcqs {A : Type v} [Finite A] (V : A → Scheme.{u})
    (S : Scheme.{u}) (g : ∀ a : A, V a ⟶ S) :
    ((∀ a : A, CompactSpace (V a)) → CompactSpace ↥(∐ V)) ∧
    ((∀ a : A, QuasiSeparatedSpace (V a)) → QuasiSeparatedSpace ↥(∐ V)) ∧
    ((∀ a : A, LocallyOfFinitePresentation (g a)) →
      LocallyOfFinitePresentation (Sigma.desc g)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hV
    let 𝒰 := sigmaOpenCover V
    let : Finite 𝒰.I₀ := by
      change Finite A
      infer_instance
    let : ∀ i, CompactSpace (𝒰.X i) := by
      intro i
      exact hV i
    exact 𝒰.compactSpace
  · intro hV
    let e := equivShrink.{u} A
    have : Finite (Shrink.{u} A) := Finite.of_equiv A e
    let V' : Shrink.{u} A → Scheme.{u} := fun a ↦ V (e.symm a)
    have : ∀ a, QuasiSeparatedSpace (V' a) := fun a ↦ hV (e.symm a)
    apply (quasiSeparatedSpace_congr (Sigma.reindex e.symm V).hom.homeomorph).mp
    apply (quasiSeparatedSpace_congr (sigmaMk V')).mp
    refine ⟨?_⟩
    intro U W hUo hUc hWo hWc
    have hcompact : ∀ a : Shrink.{u} A,
        IsCompact (Sigma.mk a '' (Sigma.mk a ⁻¹' (U ∩ W))) := by
      intro a
      apply IsCompact.image _ continuous_sigmaMk
      rw [Set.preimage_inter]
      exact (Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hUc).inter_of_isOpen
        (Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hWc)
        (hUo.preimage continuous_sigmaMk) (hWo.preimage continuous_sigmaMk)
    rw [← Set.iUnion_image_preimage_sigma_mk_eq_self (U ∩ W)]
    exact isCompact_iUnion hcompact
  · intro hg
    exact IsZariskiLocalAtSource.sigmaDesc hg

end AlgebraicGeometry
