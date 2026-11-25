/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduced.ReducedNormalization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Componentwise normalization over a normal reduction

## References

* Stacks Project, Varieties, Tags 0BXR and 0BXT
* Morphisms, Tags 035Q and 0CDV
* Stacks Project, Varieties, Tags 0BXR and 0BXT, final paragraph
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace AlgebraicGeometry

private theorem component_open_of_normal (R : Scheme.{u}) [IsLocallyNoetherian R]
    (hR : ∀ x : R, IsDomain (R.presheaf.stalk x))
    (Z : Set R) (hZ : Z ∈ irreducibleComponents R) : IsOpen Z := by
  classical
  obtain ⟨x, hx⟩ := hZ.1.nonempty
  let W : R.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have : ConnectedSpace W.toScheme :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hW (z : W.toScheme) : IsDomain (W.toScheme.presheaf.stalk z) := by
    have : IsDomain (R.presheaf.stalk (W.ι z)) := hR (W.ι z)
    let e := (asIso (W.ι.stalkMap z)).commRingCatIsoToRingEquiv
    exact e.symm.toMulEquiv.isDomain
  have : IrreducibleSpace W.toScheme := irreducibleSpace_of_isDomain_stalk _ hW
  have hWIr : IsIrreducible (W : Set R) := by
    simpa only [Set.image_univ, Scheme.Opens.range_ι] using
      (show IsIrreducible (Set.univ : Set W.toScheme) from
        IrreducibleSpace.isIrreducible_univ _).image
        W.ι W.ι.continuous.continuousOn
  have hZW : Z ⊆ W := hZ.1.isConnected.subset_connectedComponent hx
  have heq : Z = (W : Set R) := hZW.antisymm (hZ.2 hWIr hZW)
  rw [heq]
  exact W.isOpen

private theorem closed_component_openImmersion {C R : Scheme.{u}} [IsLocallyNoetherian R]
    (hR : ∀ x : R, IsDomain (R.presheaf.stalk x))
    (a : C ⟶ R) [IsClosedImmersion a]
    (ha : Set.range a ∈ irreducibleComponents R) : IsOpenImmersion a := by
  have (x : R) : IsDomain (R.presheaf.stalk x) := hR x
  have : IsReduced R := isReduced_of_isReduced_stalk R
  let W : R.Opens := ⟨Set.range a, component_open_of_normal R hR _ ha⟩
  let g := IsOpenImmersion.lift W.ι a (by simp [W])
  have hg : g ≫ W.ι = a := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (g ≫ W.ι) := by rw [hg]; infer_instance
  have : IsClosedImmersion g := IsClosedImmersion.of_comp g W.ι
  have : Surjective g := ⟨fun y => by
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, W.ι.isOpenEmbedding.injective ?_⟩
    change (g ≫ W.ι) x = y.1
    rwa [hg]⟩
  have : IsIso g := isIso_of_isClosedImmersion_of_surjective g
  rw [← hg]
  infer_instance

private theorem reduction_homeomorph (T : Scheme.{u}) : IsHomeomorph T.nilradical.subschemeι := by
  apply isHomeomorph_iff_isEmbedding_surjective.mpr
  refine ⟨T.nilradical.subschemeι.isClosedEmbedding.isEmbedding, ?_⟩
  intro x
  change x ∈ Set.range T.nilradical.subschemeι
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
  trivial

private theorem dense_open_component_nonempty (T : Scheme.{u}) [IsNoetherian T]
    (U : T.Opens) (hU : Dense (U : Set T))
    (Z : Set T) (hZ : Z ∈ irreducibleComponents T) :
    (Z ∩ Set.range U.ι).Nonempty := by
  classical
  have hfinite := finite_irreducibleComponents_of_isNoetherian (X := T)
  let W : T.Opens := ⟨(⋃₀ (irreducibleComponents T \ {Z}))ᶜ, by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfinite.sdiff.isClosed_biUnion
      (fun V hV => isClosed_of_mem_irreducibleComponents V hV.1)⟩
  have hW : closure (W : Set T) = Z :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hfinite Z hZ
  have hWne : (W : Set T).Nonempty := by
    by_contra! he
    exact hZ.1.nonempty.ne_empty (by rw [← hW, he, closure_empty])
  obtain ⟨x, hxW, hxU⟩ := hU.inter_open_nonempty W W.isOpen hWne
  refine ⟨x, ?_, ?_⟩
  · rw [← hW]; exact subset_closure hxW
  · simpa only [Scheme.Opens.range_ι] using hxU

private theorem component_to_normal_reduction_openImmersion
    {C T : Scheme.{u}} [IsIntegral C] [IsNoetherian T]
    (a : C ⟶ T) [IsClosedImmersion a]
    (ha : Set.range a ∈ irreducibleComponents T)
    (U : T.Opens) (hU : Dense (U : Set T))
    (hR : ∀ x : U.toScheme.nilradical.subscheme,
      IsDomain (U.toScheme.nilradical.subscheme.presheaf.stalk x)) :
    IsOpenImmersion (a ∣_ U).liftNilradical := by
  let R := U.toScheme.nilradical.subscheme
  let j := U.toScheme.nilradical.subschemeι
  let r := (a ∣_ U).liftNilradical
  have hfac : r ≫ j = a ∣_ U := by simp [r,j]
  have : IsLocallyNoetherian R := LocallyOfFiniteType.isLocallyNoetherian j
  have : IsClosedImmersion (r ≫ j) := by rw [hfac]; infer_instance
  have : IsClosedImmersion r := IsClosedImmersion.of_comp_isClosedImmersion r j
  have h1 := preimage_mem_irreducibleComponents ha U.ι.isOpenEmbedding
    (dense_open_component_nonempty T U hU _ ha)
  have hj := reduction_homeomorph U.toScheme
  have h2 := preimage_mem_irreducibleComponents h1 hj.isOpenEmbedding (by
    simpa only [hj.surjective.range_eq, Set.inter_univ] using h1.1.nonempty)
  have heq : Set.range r = j ⁻¹' (U.ι ⁻¹' Set.range a) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      change U.ι (j (r x)) ∈ Set.range a
      change U.ι ((r ≫ j) x) ∈ Set.range a
      rw [hfac]
      exact ⟨x.1, (morphismRestrict_base_coe a U x).symm⟩
    · intro hy
      obtain ⟨x,hx⟩ := hy
      let xU : a ⁻¹ᵁ U := ⟨x, by change a x ∈ U; rw [hx]; exact (j y).2⟩
      refine ⟨xU, j.isClosedEmbedding.injective ?_⟩
      change (r ≫ j) xU = j y
      rw [hfac]
      apply Subtype.ext
      simpa only [morphismRestrict_base_coe, xU, Scheme.Opens.ι_apply] using hx
  exact closed_component_openImmersion hR r (heq.symm ▸ h2)

private theorem normalized_component_openImmersion
    {C T : Scheme.{u}} [IsIntegral C] [IsNoetherian T]
    (a : C ⟶ T) [IsClosedImmersion a]
    (ha : Set.range a ∈ irreducibleComponents T)
    (U : T.Opens) (hU : Dense (U : Set T))
    (hR : ∀ x : U.toScheme.nilradical.subscheme,
      IsDomain (U.toScheme.nilradical.subscheme.presheaf.stalk x) ∧
        IsIntegrallyClosed (U.toScheme.nilradical.subscheme.presheaf.stalk x)) :
    IsOpenImmersion ((C.fromNormalization ≫ a) ∣_ U).liftNilradical := by
  let R := U.toScheme.nilradical.subscheme
  let j := U.toScheme.nilradical.subschemeι
  let r := (a ∣_ U).liftNilradical
  have : IsOpenImmersion r := component_to_normal_reduction_openImmersion
    a ha U hU (fun x => (hR x).1)
  have hnorm : IsIso (C.fromNormalization ∣_ a ⁻¹ᵁ U) := by
    apply C.isIso_fromNormalization_restrict
    intro x hx
    let xu : a ⁻¹ᵁ U := ⟨x,hx⟩
    have : IsIntegrallyClosed (R.presheaf.stalk (r xu)) := (hR (r xu)).2
    let er := (asIso (r.stalkMap xu)).commRingCatIsoToRingEquiv
    let ec := (asIso ((a ⁻¹ᵁ U).ι.stalkMap xu)).commRingCatIsoToRingEquiv
    exact IsIntegrallyClosed.of_equiv (er.trans ec.symm)
  have heq : ((C.fromNormalization ≫ a) ∣_ U).liftNilradical =
      (C.fromNormalization ∣_ a ⁻¹ᵁ U) ≫ r := by
    apply (cancel_mono j).mp
    simp only [Category.assoc, Scheme.Hom.liftNilradical_subschemeι,
      ← morphismRestrict_comp, r,j]
  rw [heq]
  infer_instance

private theorem range_liftNilradical_restrict
    {C T : Scheme.{u}} [IsReduced C] (a : C ⟶ T) (U : T.Opens) :
    Set.range (a ∣_ U).liftNilradical =
      U.toScheme.nilradical.subschemeι ⁻¹' (U.ι ⁻¹' Set.range a) := by
  let j := U.toScheme.nilradical.subschemeι
  let r := (a ∣_ U).liftNilradical
  have hfac : r ≫ j = a ∣_ U := by simp [r,j]
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    change U.ι (j (r x)) ∈ Set.range a
    change U.ι ((r ≫ j) x) ∈ Set.range a
    rw [hfac]
    exact ⟨x.1, (morphismRestrict_base_coe a U x).symm⟩
  · intro hy
    obtain ⟨x,hx⟩ := hy
    let xU : a ⁻¹ᵁ U := ⟨x, by change a x ∈ U; rw [hx]; exact (j y).2⟩
    refine ⟨xU, j.isClosedEmbedding.injective ?_⟩
    change (r ≫ j) xU = j y
    rw [hfac]
    apply Subtype.ext
    simpa only [morphismRestrict_base_coe, xU, Scheme.Opens.ι_apply] using hx

private theorem disjoint_normal_components
    (R : Scheme.{u}) [IsLocallyNoetherian R]
    (hR : ∀ x : R, IsDomain (R.presheaf.stalk x))
    {Z W : Set R} (hZ : Z ∈ irreducibleComponents R)
    (hW : W ∈ irreducibleComponents R) (hne : Z ≠ W) : Disjoint Z W := by
  rw [Set.disjoint_left]
  intro x hxZ hxW
  have hWZ : W ⊆ Z := by
    have h := subset_closure_inter_of_isPreirreducible_of_isOpen hW.1.2
      (component_open_of_normal R hR Z hZ) ⟨x,hxW,hxZ⟩
    exact h.trans (closure_minimal Set.inter_subset_right
      (isClosed_of_mem_irreducibleComponents _ hZ))
  exact hne (hW.2 hZ.1 hWZ |>.antisymm hWZ)

namespace Scheme

/-- Over an open whose reduction is normal, componentwise normalization is that
reduction, with the comparison preserving the map to the open. -/
theorem reducedNormalization_over_normal_reduction
    {k : Type u} [Field k] (T : Scheme.{u}) (q : T ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (U : T.Opens) (hU : Dense (U : Set T))
    (hnormal : ∀ z : U.toScheme.nilradical.subscheme,
      IsDomain (U.toScheme.nilradical.subscheme.presheaf.stalk z) ∧
        IsIntegrallyClosed (U.toScheme.nilradical.subscheme.presheaf.stalk z)) :
    ∃ e : (T.fromReducedNormalization ⁻¹ᵁ U).toScheme ≅ U.toScheme.nilradical.subscheme,
      e.hom ≫ U.toScheme.nilradical.subschemeι = T.fromReducedNormalization ∣_ U := by
  classical
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian T := ⟨⟩
  have : Finite (irreducibleComponents T) :=
    (finite_irreducibleComponents_of_isNoetherian (X := T)).to_subtype
  let R := U.toScheme.nilradical.subscheme
  let j := U.toScheme.nilradical.subschemeι
  have : IsLocallyNoetherian R := LocallyOfFiniteType.isLocallyNoetherian j
  let C (Z : irreducibleComponents T) := T.reducedNormalizationComponent Z
  let c (Z : irreducibleComponents T) : C Z ⟶ T :=
    (Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι
  have hc (Z : irreducibleComponents T) : Set.range (c Z) = Z.1 := by
    change Set.range (Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  let G (Z : irreducibleComponents T) := (C Z).normalization
  let g (Z : irreducibleComponents T) : G Z ⟶ T := (C Z).fromNormalization ≫ c Z
  have hg (Z : irreducibleComponents T) : Set.range (g Z) = Z.1 := by
    rw [show Set.range (g Z) = Set.range (c Z) from by
      ext x
      constructor
      · rintro ⟨y,rfl⟩; exact ⟨(C Z).fromNormalization y,rfl⟩
      · rintro ⟨y,rfl⟩
        obtain ⟨z,rfl⟩ := (C Z).fromNormalization.surjective y
        exact ⟨z,rfl⟩]
    exact hc Z
  let b (Z : irreducibleComponents T) : (g Z ⁻¹ᵁ U).toScheme ⟶ R :=
    (g Z ∣_ U).liftNilradical
  have hbopen (Z) : IsOpenImmersion (b Z) :=
    normalized_component_openImmersion (c Z) ((hc Z).symm ▸ Z.2) U hU hnormal
  have hbrange (Z) : Set.range (b Z) = j ⁻¹' (U.ι ⁻¹' Z.1) := by
    simpa only [b, hg] using range_liftNilradical_restrict (g Z) U
  have hj := reduction_homeomorph U.toScheme
  have hcomp (Z : irreducibleComponents T) :
      Set.range (b Z) ∈ irreducibleComponents R := by
    rw [hbrange]
    have h1 := preimage_mem_irreducibleComponents Z.2 U.ι.isOpenEmbedding
      (dense_open_component_nonempty T U hU Z.1 Z.2)
    exact preimage_mem_irreducibleComponents h1 hj.isOpenEmbedding (by
      simpa only [j, hj.surjective.range_eq, Set.inter_univ] using h1.1.nonempty)
  have hrinj : Function.Injective (fun Z => Set.range (b Z)) := by
    intro Z W he
    have he' : U.ι ⁻¹' Z.1 = U.ι ⁻¹' W.1 := by
      apply Set.preimage_injective.mpr hj.surjective
      simpa only [hbrange] using he
    have hh (V : irreducibleComponents T) :
        closure (U.ι '' (U.ι ⁻¹' V.1)) = V.1 := by
      apply closure_image_preimage_of_isPreirreducible U.ι U.ι.isOpenEmbedding.isOpenMap
      · obtain ⟨x,hxV,y,hy⟩ := dense_open_component_nonempty T U hU V.1 V.2
        exact ⟨y, show U.ι y ∈ V.1 by rwa [hy]⟩
      · exact V.2.1.2
      · exact isClosed_of_mem_irreducibleComponents _ V.2
    apply Subtype.ext
    rw [← hh Z, ← hh W, he']
  have hbiso : IsIso (Sigma.desc b) := by
    apply (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk R b)).mp
    apply nonempty_isColimit_cofanMk_of
    · apply TopologicalSpace.Opens.ext
      ext x
      simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion,
        TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      let Z : irreducibleComponents T := ⟨irreducibleComponent (U.ι (j x)),
        irreducibleComponent_mem_irreducibleComponents _⟩
      refine ⟨Z, ?_⟩
      change x ∈ Set.range (b Z)
      rw [hbrange]
      exact mem_irreducibleComponent
    · intro Z W hne
      apply disjoint_iff.mpr
      apply TopologicalSpace.Opens.ext
      ext x
      change (x ∈ Set.range (b Z) ∧ x ∈ Set.range (b W)) ↔ False
      exact ⟨fun hx => Set.disjoint_left.mp
        (disjoint_normal_components R (fun x => (hnormal x).1)
          (hcomp Z) (hcomp W) (fun he => hne (hrinj he))) hx.1 hx.2,
        False.elim⟩
  let a (Z : irreducibleComponents T) : (g Z ⁻¹ᵁ U).toScheme ⟶
      (T.fromReducedNormalization ⁻¹ᵁ U).toScheme :=
    (Sigma.ι G Z).resLE _ _ (by
      change g Z ⁻¹ᵁ U ≤ (Sigma.ι G Z) ⁻¹ᵁ T.fromReducedNormalization ⁻¹ᵁ U
      rw [← Scheme.Hom.comp_preimage]
      change g Z ⁻¹ᵁ U ≤ (Sigma.ι G Z ≫ Sigma.desc g) ⁻¹ᵁ U
      simp)
  have haiso : IsIso (Sigma.desc a) := by
    have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct G)
    have hcol : Nonempty (IsColimit (Cofan.mk _ a)) := by
      apply hau (Cofan.mk _ a)
        (Discrete.natTrans fun i => (g i.as ⁻¹ᵁ U).ι)
        (T.fromReducedNormalization ⁻¹ᵁ U).ι
      · ext Z; simp [a]
      · exact NatTrans.Equifibered.of_discrete _
      · intro Z
        change IsPullback (a Z.as) (g Z.as ⁻¹ᵁ U).ι
          (T.fromReducedNormalization ⁻¹ᵁ U).ι (Sigma.ι G Z.as)
        apply IsOpenImmersion.isPullback
        · simp [a]
        · simp only [Scheme.Opens.opensRange_ι]
          rw [← Scheme.Hom.comp_preimage]
          change (Sigma.ι G Z.as ≫ Sigma.desc g) ⁻¹ᵁ U = g Z.as ⁻¹ᵁ U
          rw [Sigma.ι_comp_desc]
    exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hcol
  let e := (asIso (Sigma.desc a)).symm ≪≫ asIso (Sigma.desc b)
  refine ⟨e, ?_⟩
  apply (cancel_epi (Sigma.desc a)).mp
  simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, ← Category.assoc,
    IsIso.hom_inv_id, Category.id_comp]
  apply Sigma.hom_ext
  intro Z
  rw [← Category.assoc, Sigma.ι_comp_desc, ← Category.assoc, Sigma.ι_comp_desc]
  change b Z ≫ j = a Z ≫ T.fromReducedNormalization ∣_ U
  apply (cancel_mono U.ι).mp
  simp [b, j, a, Scheme.fromReducedNormalization, G, g, C, c]

end Scheme

end AlgebraicGeometry
