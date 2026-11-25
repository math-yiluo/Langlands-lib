/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The reduction is a universal homeomorphism

Source: literature/stacks-project/morphisms.tex, Lemma 054M.
(blueprint: lem-weil-pbc-reduction-universal-homeomorphism).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The reduction is reduced and its canonical map is a surjective closed immersion
and a universal homeomorphism. The proof follows Stacks Lemma 054M and Lemma 01J3.
Source: Stacks Project, Morphisms, Lemma 054M; Schemes, Lemma 01J3 / Definition 01J4.
(blueprint: lem-weil-pbc-reduction-universal-homeomorphism).
Proof:
1. By def-weil-pbc-scheme-reduction the map is the nilradical closed immersion
   (def-weil-closed-immersion). Every prime contains the nilradical, so its support
   is all of X and the map is surjective (def-weil-surjective-morphism).
   A closed embedding onto all of X is a homeomorphism.
2. On an affine open Spec R (def-weil-affine-spectrum), the inverse image is
   Spec (R / nilradical R). If a class is nilpotent, a power of its representative
   belongs to the nilradical, so a further power is zero; the representative itself
   is therefore in the nilradical. The quotient is reduced. Apply
   lem-weil-pbc-affine-scheme-reduced-iff on this affine cover, and hence all local
   rings are reduced (def-pc-reduced-scheme), as in Stacks 01J3 for the full subset.
3. For every morphism X' → X, its fibre product (def-pc-fibre-product) projection
   is a closed immersion by lem-weil-pbc-closed-immersion-base-change and surjective
   by lem-weil-pbc-surjective-base-change. Its underlying closed embedding is
   surjective and therefore a homeomorphism. This is exactly
   def-weil-universal-homeomorphism. -/
theorem reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism
    (X : Scheme.{u}) :
    IsReduced X.nilradical.subscheme ∧
      IsClosedImmersion X.nilradical.subschemeι ∧
        Surjective X.nilradical.subschemeι ∧
          (topologically IsHomeomorph).universally X.nilradical.subschemeι := by
  have hsurj : Surjective X.nilradical.subschemeι := by
    constructor
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.support_nilradical]
    rfl
  refine ⟨inferInstance, inferInstance, hsurj, ?_⟩
  intro X' Y' i₁ i₂ f' h
  have : IsClosedImmersion f' :=
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback
      h.flip (inferInstance : IsClosedImmersion X.nilradical.subschemeι)
  have : Surjective f' :=
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback h.flip hsurj
  exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨f'.isEmbedding, f'.surjective⟩

end AlgebraicGeometry
