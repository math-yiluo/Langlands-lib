/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import WeilConjectures.RingTheory.GenericFlatness

/-! # Generic flatness on an affine source chart

Source: Stacks Project, Tags 051T and 052A.
(blueprint: lem-sbc-affine-chart-generic-flatness)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine finite type chart over an affine integral base becomes flat on a basic open.

Source: Stacks Project, Tag 051T applied to the algebra itself, and Tag 052A.
Proof: let A and B be the global section rings of S and X. The induced map
A → B is finite type, and A is a domain. Apply the algebraic generic-flatness
lemma to obtain a nonzero a such that the composite A → B → B[1/a] is flat.
The global sections of the affine basic open V = D(f.appTop(a)) in X are a
localization of B at f.appTop(a). Thus V → S is flat by the affine ring-map
criterion. The preimage of D(a) under f is V. Factoring V → S through the open
immersion D(a) → S preserves flatness of the factor, giving the claim.
The zero target algebra is allowed; its localization and its empty spectrum
satisfy the same criteria. No quasi-compactness or Noetherian assumption is used.

(blueprint: lem-sbc-affine-chart-generic-flatness) -/
theorem exists_nonzero_flat_restrict_basicOpen {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] [IsIntegral S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ a : Γ(S, ⊤), a ≠ 0 ∧ Flat (f ∣_ S.basicOpen a) := by
  obtain ⟨a, ha, hflat⟩ := RingHom.exists_nonzero_flat_localizationAway f.appTop.hom
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance)
  refine ⟨a, ha, ?_⟩
  let V : X.Opens := X.basicOpen (f.appTop a)
  have : IsAffine V.toScheme := (isAffineOpen_top X).basicOpen _
  have h : Flat (V.ι ≫ f) := by
    apply (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mpr
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    convert hflat Γ(V, ⊤) using 1
  apply MorphismProperty.of_postcomp @Flat (W' := @IsOpenImmersion)
    (f ∣_ S.basicOpen a) (S.basicOpen a).ι inferInstance
  rw [morphismRestrict_ι]
  have heq : f ⁻¹ᵁ S.basicOpen a = V := by
    simpa only [Scheme.Hom.appTop, Scheme.Hom.preimage_top] using Scheme.preimage_basicOpen f a
  rw [heq]
  exact h

end AlgebraicGeometry
