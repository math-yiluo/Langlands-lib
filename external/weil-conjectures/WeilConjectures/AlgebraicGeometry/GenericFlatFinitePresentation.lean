/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Properties

import WeilConjectures.AlgebraicGeometry.GenericFlatness
import WeilConjectures.AlgebraicGeometry.GenericLocallyOfFinitePresentation

/-! # Generic flatness with finite presentation

Source: Stacks Project, Tag 052A.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A finite type map to an integral scheme is flat and locally finitely presented
on a nonempty open of the base.

Source: Stacks Project, Tag 052A, applied to the structure sheaf.
Proof: replace the integral base by a nonempty affine open Spec A, where A is a
domain. Cover its inverse image by finitely many affine opens Spec B_i, using
quasi-compactness. Each B_i is a finite type A-algebra. Tag 051T, applied with
M = B_i, gives a nonzero a_i in A such that (B_i)_{a_i} is free over A_{a_i}
and finitely presented as an A_{a_i}-algebra. Invert the product of these finitely
many a_i. This product is nonzero, so its basic open is nonempty. Flatness and
local finite presentation hold on the resulting affine cover of the inverse
image, hence hold for the restricted map by locality on the source. If the
inverse image is empty, use the empty product 1; both properties are vacuous.
No noetherianity or separatedness hypothesis is needed.

(blueprint: lem-sbc-generic-flat-finite-presentation) -/
theorem exists_nonempty_open_flat_finitePresentation_restrict {X S : Scheme.{u}}
    [IsIntegral S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ Flat (f ∣_ U) ∧
      LocallyOfFinitePresentation (f ∣_ U) := by
  obtain ⟨U₁, hU₁, hflat⟩ := exists_nonempty_open_flat_restrict f
  obtain ⟨U₂, hU₂, hfp⟩ := exists_nonempty_open_locallyOfFinitePresentation_restrict f
  have hη₁ : genericPoint S ∈ U₁ := by
    apply ((genericPoint_spec S).mem_open_set_iff U₁.isOpen).mpr
    simpa only [Set.univ_inter] using hU₁
  have hη₂ : genericPoint S ∈ U₂ := by
    apply ((genericPoint_spec S).mem_open_set_iff U₂.isOpen).mpr
    simpa only [Set.univ_inter] using hU₂
  let U : S.Opens := U₁ ⊓ U₂
  have hU : (U : Set S).Nonempty := ⟨genericPoint S, hη₁, hη₂⟩
  have himage (V : S.Opens) (hUV : U ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ U = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUV hx⟩, hx, rfl⟩
  refine ⟨U, hU, ?_, ?_⟩
  · have h : Flat ((f ∣_ U₁) ∣_ (U₁.ι ⁻¹ᵁ U)) :=
      IsZariskiLocalAtTarget.restrict hflat _
    have h' := (MorphismProperty.arrow_mk_iso_iff @Flat
      (morphismRestrictRestrict f U₁ (U₁.ι ⁻¹ᵁ U))).mp h
    rwa [himage U₁ inf_le_left] at h'
  · have h : LocallyOfFinitePresentation ((f ∣_ U₂) ∣_ (U₂.ι ⁻¹ᵁ U)) :=
      IsZariskiLocalAtTarget.restrict hfp _
    have h' := (MorphismProperty.arrow_mk_iso_iff @LocallyOfFinitePresentation
      (morphismRestrictRestrict f U₂ (U₂.ι ⁻¹ᵁ U))).mp h
    rwa [himage U₂ inf_le_right] at h'

end AlgebraicGeometry
