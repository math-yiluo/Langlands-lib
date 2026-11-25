/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.SeparatedOpenInduction

@[expose] public section

universe u

open TopologicalSpace

namespace AlgebraicGeometry

/-- The intersection property needed for quasi-compact open induction.

The overlap of a quasi-compact open with an affine open is separated and quasi-compact;
applying separated quasi-compact open induction proves `P` on the overlap. Source:
literature/stacks-project/coherent.tex, Cohomology of Schemes, Lemma 08DR (blueprint:
lem-sc-invert-s-cohomology-induction), second paragraph.
(blueprint: property-intersection-qc-affine)

Proof: The intersection is quasi-compact by quasi-separatedness and finite affine cover criteria,
and separated as an open subscheme of affine V; apply separated_quasiCompact_open_induction. -/
theorem property_intersection_of_quasiCompact_affine
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (P : X.Opens → Prop)
    (h_affine : ∀ U : X.Opens, IsAffineOpen U → P U)
    (h_union : ∀ (U V : X.Opens), IsCompact (U : Set X) → IsAffineOpen V →
      P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V) :
    P (U ⊓ V) := by
  have hW_qc : IsCompact ((U ⊓ V : X.Opens) : Set X) := by
    change IsCompact ((U : Set X) ∩ (V : Set X))
    exact QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU V.2 hV.isCompact
  let : IsAffine V.toScheme := hV
  let f : (U ⊓ V).toScheme ⟶ V.toScheme :=
    X.homOfLE (show U ⊓ V ≤ V from inf_le_right)
  have hW_sep : (U ⊓ V).toScheme.IsSeparated := by
    constructor
    simpa only [CategoryTheory.Limits.terminal.comp_from] using
      (inferInstance : IsSeparated (CategoryTheory.CategoryStruct.comp f
        (CategoryTheory.Limits.terminal.from V.toScheme)))
  exact separated_quasiCompact_open_induction X P h_affine h_union (U ⊓ V) hW_qc hW_sep

end AlgebraicGeometry
