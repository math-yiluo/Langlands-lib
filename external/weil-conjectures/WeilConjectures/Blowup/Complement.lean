/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!

# The blow-up is an isomorphism away from the center

We show that the blow-up map `I.blowupMap : I.blowup ⟶ X` of a scheme `X` along a
quasi-coherent ideal `I : X.IdealSheafData` is an isomorphism over the complement of the
support of `I`.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.isIso_blowupMap_restrict` — the blow-up map is an
  isomorphism over any open disjoint from the support of the ideal.
- `AlgebraicGeometry.Scheme.IdealSheafData.isIso_blowupMap_restrict_support_compl` — the
  blow-up map is an isomorphism over the complement of the support
  (blueprint: `thm:nagata-global-blowup-complement`).

-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The blow-up map is an isomorphism over any affine open on which the ideal is the unit
ideal. (blueprint: `lemma:nagata-affine-blowup-complement`) -/
lemma isIso_blowupMap_restrict_of_ideal_eq_top {U : X.affineOpens}
    (h : I.ideal U = ⊤) : IsIso (I.blowupMap ∣_ U.1) := by
  have hiso : IsIso (I.blowupNatTrans.app U) := by
    rw [I.blowupNatTrans_app U]
    have := AffineBlowup.isIso_toSpec_of_eq_top h
    infer_instance
  have e : Arrow.mk (I.blowupMap ∣_ U.1.ι.opensRange) ≅ Arrow.mk (I.blowupNatTrans.app U) :=
    morphismRestrictArrowIso I.blowupMap (I.blowupNatTrans.app U) (I.blowupι_blowupMap U)
      (by rw [Scheme.Opens.opensRange_ι]; exact I.blowupMap_preimage U)
  have H : IsIso (I.blowupMap ∣_ U.1.ι.opensRange) := by
    rw [← MorphismProperty.isomorphisms.iff,
      (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e,
      MorphismProperty.isomorphisms.iff]
    exact hiso
  rwa [Scheme.Opens.opensRange_ι] at H

/-- **The blow-up is an isomorphism away from the center**, general form: the blow-up map
is an isomorphism over any open disjoint from the support of the ideal.
(blueprint: `thm:nagata-global-blowup-complement`) -/
theorem isIso_blowupMap_restrict {U : X.Opens}
    (hU : Disjoint (U : Set X) (I.support : Set X)) :
    IsIso (I.blowupMap ∣_ U) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun W : {W : X.affineOpens // W.1 ≤ U} ↦ U.ι ⁻¹ᵁ W.1.1) ?_ fun W ↦ ?_
  · have hsup : (⨆ W : {W : X.affineOpens // W.1 ≤ U}, W.1.1) = U := by
      refine le_antisymm (iSup_le fun W ↦ W.2) fun x hx ↦ ?_
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
      exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    rw [← Scheme.Hom.preimage_iSup, hsup, Scheme.Opens.ι_preimage_self]
  · have him : U.ι ''ᵁ (U.ι ⁻¹ᵁ W.1.1) = W.1.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr W.2
    rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
        (morphismRestrictRestrict I.blowupMap U (U.ι ⁻¹ᵁ W.1.1) ≪≫
          morphismRestrictEq I.blowupMap him),
      MorphismProperty.isomorphisms.iff]
    exact I.isIso_blowupMap_restrict_of_ideal_eq_top
      (I.ideal_eq_top_of_disjoint_support (hU.mono_left W.2))

/-- **The blow-up is an isomorphism away from the center**: the blow-up map is an
isomorphism over the complement of the support of the ideal.
(blueprint: `thm:nagata-global-blowup-complement`) -/
theorem isIso_blowupMap_restrict_support_compl :
    IsIso (I.blowupMap ∣_ I.support.compl) :=
  isIso_blowupMap_restrict I (by simpa using disjoint_compl_left)

end AlgebraicGeometry.Scheme.IdealSheafData
