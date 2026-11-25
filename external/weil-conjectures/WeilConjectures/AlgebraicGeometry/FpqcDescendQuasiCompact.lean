/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Quasi-compactness descends along flat surjective quasi-compact morphisms

Source: literature/stacks-project/descent.tex, Descent, Lemma Tag 02KQ
(lemma-descending-property-quasi-compact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Quasi-compactness descends along a surjective, quasi-compact morphism (in particular along a
flat, surjective, quasi-compact one; flatness is not needed).

The proof follows Descent, Lemma Tag 02KQ.  For an affine open `U` of `S`,
put `V := g ⁻¹' U`; quasi-compactness of `g` makes `V` quasi-compact.  Put
`X' := X ×ₛ S'` and `W := f' ⁻¹' V`, where `f'` is the second projection;
quasi-compactness of `f'` and the quasi-compact-open preimage lemma make `W`
quasi-compact.  The projection `X' ⟶ X` is surjective by base change of `g`,
and its image of `W` is exactly `f ⁻¹' U`.  This image is quasi-compact by
continuity of the projection and the continuous-image lemma.  Since this holds
for every affine `U`, the definition of `QuasiCompact f` concludes.
-/
theorem quasiCompact_of_fpqc_baseChange {S S' X : Scheme.{u}} (g : S' ⟶ S)
    [Surjective g] [QuasiCompact g] (f : X ⟶ S)
    [QuasiCompact (pullback.snd f g)] : QuasiCompact f := by
  apply quasiCompact_iff_forall_isAffineOpen.mpr
  intro U hU
  have hV : IsCompact (g ⁻¹' (U : Set S)) :=
    QuasiCompact.isCompact_preimage _ U.isOpen hU.isCompact
  have hW : IsCompact ((pullback.snd f g) ⁻¹' (g ⁻¹' (U : Set S))) :=
    QuasiCompact.isCompact_preimage _ (U.isOpen.preimage g.continuous) hV
  have heq : (pullback.fst f g) ⁻¹' (f ⁻¹' (U : Set S)) =
      (pullback.snd f g) ⁻¹' (g ⁻¹' (U : Set S)) := by
    rw [← Set.preimage_comp, ← Set.preimage_comp]
    change (pullback.fst f g ≫ f) ⁻¹' (U : Set S) = (pullback.snd f g ≫ g) ⁻¹' (U : Set S)
    rw [pullback.condition]
  rw [← heq] at hW
  have himage := hW.image (pullback.fst f g).continuous
  rwa [Set.image_preimage_eq _ (pullback.fst f g).surjective] at himage

end AlgebraicGeometry
