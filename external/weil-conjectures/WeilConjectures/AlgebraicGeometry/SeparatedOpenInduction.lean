/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Induction principle for separated quasi-compact opens

Source: Stacks Project, Cohomology of Schemes, Lemma 08DR (coherent-lemma-induction-principle),
proof, first induction for separated quasi-compact opens
(blueprint: lem-sc-invert-s-cohomology-separated-induction).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A property holding on affine opens and stable under gluing a quasi-compact open with an
affine open holds on every separated quasi-compact open. Source: Stacks Project, Cohomology of
Schemes, Lemma 08DR (coherent-lemma-induction-principle), proof, first induction for separated
quasi-compact opens (blueprint: lem-sc-invert-s-cohomology-separated-induction).

Proof: choose a finite affine cover of `W` and induct on its cardinality; the empty open is
affine. Adjoin the last affine `V` to the union `U` of the preceding charts. Each chart's
intersection with `V` is affine by separatedness of `W`, so `U` and `U ∩ V` are separated
quasi-compact opens with shorter affine covers and satisfy `P` by induction; `V` satisfies `P`
as an affine open. The gluing hypothesis gives `P (U ∪ V)`. -/
theorem separated_quasiCompact_open_induction (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (P : X.Opens → Prop)
    (h_affine : ∀ U : X.Opens, IsAffineOpen U → P U)
    (h_union : ∀ (U V : X.Opens), IsCompact (U : Set X) → IsAffineOpen V →
      P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (W : X.Opens) (hW_qc : IsCompact (W : Set X)) (hW_sep : W.toScheme.IsSeparated) : P W := by
  have : W.toScheme.IsSeparated := hW_sep
  have h_inf (A B : X.Opens) (hA : IsAffineOpen A) (hB : IsAffineOpen B)
      (hAW : A ≤ W) (hBW : B ≤ W) : IsAffineOpen (A ⊓ B) := by
    have hA' := hA.preimage_of_isOpenImmersion W.ι (by simpa using hAW)
    have hB' := hB.preimage_of_isOpenImmersion W.ι (by simpa using hBW)
    have h := (hA'.inf hB').image_of_isOpenImmersion W.ι
    rw [← Scheme.Hom.preimage_inf, Scheme.Hom.image_preimage_eq_opensRange_inf] at h
    simpa [inf_eq_right.mpr (inf_le_left.trans hAW)] using h
  -- Strengthen the induction to include intersections with every affine open inside W.
  have h := compact_open_induction_on (P := fun U ↦ U ≤ W →
      P U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ W → P (U ⊓ V)) W hW_qc ?_ ?_
  · exact (h le_rfl).1
  · intro _
    exact ⟨h_affine _ (isAffineOpen_bot X), fun V _ _ ↦ by
      simpa using h_affine _ (isAffineOpen_bot X)⟩
  · intro U hU V ih hUW
    have hUle : U ≤ W := le_sup_left.trans hUW
    have hVle : (V : X.Opens) ≤ W := le_sup_right.trans hUW
    obtain ⟨hPU, hPI⟩ := ih hUle
    refine ⟨h_union U V hU V.property hPU (h_affine _ V.property)
      (hPI V V.property hVle), ?_⟩
    intro T hT hTW
    have hVT := h_inf V T V.property hT hVle hTW
    have hUT : IsCompact ((U ⊓ T : X.Opens) : Set X) :=
      hU.inter_of_isOpen hT.isCompact U.isOpen T.isOpen
    rw [inf_sup_right]
    apply h_union (U ⊓ T) (V ⊓ T) hUT hVT (hPI T hT hTW) (h_affine _ hVT)
    simpa [inf_assoc, inf_left_comm, inf_comm] using
      hPI (V ⊓ T) hVT (inf_le_left.trans hVle)

end AlgebraicGeometry
