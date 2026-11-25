/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!

# Isomorphisms of reduced closed subschemes

An isomorphism of schemes `φ : X ≅ Y` mapping a closed subset `Z` of `X` onto a closed subset
`W` of `Y` restricts to an isomorphism of the reduced induced closed subschemes
(`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdealSubschemeIso`), compatible with the
closed immersions into `X` and `Y`. In particular an automorphism of `X` stabilizing `Z` induces
an automorphism of the reduced closed subscheme on `Z`.

-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- If `f` maps the closed subset `Z` into the closed subset `W`, the vanishing ideal of `W` is
contained in the pushforward along `f` of the vanishing ideal of `Z`. -/
lemma vanishingIdeal_le_map_vanishingIdeal (f : X ⟶ Y) {Z : Closeds X} {W : Closeds Y}
    (h : f.base '' Z ⊆ W) : vanishingIdeal W ≤ (vanishingIdeal Z).map f := by
  rw [map_vanishingIdeal]
  exact vanishingIdeal_antimono (Closeds.closure_le.2 h)

/-- An isomorphism `φ : X ≅ Y` with `φ(Z) = W` restricts to an isomorphism of the reduced
induced closed subschemes on `Z` and `W`. -/
noncomputable def vanishingIdealSubschemeIso (φ : X ≅ Y) {Z : Closeds X} {W : Closeds Y}
    (h : φ.hom.base '' Z = W) :
    (vanishingIdeal Z).subscheme ≅ (vanishingIdeal W).subscheme where
  hom := subschemeMap _ _ φ.hom (vanishingIdeal_le_map_vanishingIdeal _ h.le)
  inv := subschemeMap _ _ φ.inv (vanishingIdeal_le_map_vanishingIdeal _ (by
    rw [← h, Set.image_image]
    simp [← Scheme.Hom.comp_apply]))
  hom_inv_id := by
    rw [← cancel_mono (vanishingIdeal Z).subschemeι]
    simp
  inv_hom_id := by
    rw [← cancel_mono (vanishingIdeal W).subschemeι]
    simp

@[reassoc (attr := simp)]
lemma vanishingIdealSubschemeIso_hom_subschemeι (φ : X ≅ Y) {Z : Closeds X} {W : Closeds Y}
    (h : φ.hom.base '' Z = W) :
    (vanishingIdealSubschemeIso φ h).hom ≫ (vanishingIdeal W).subschemeι =
      (vanishingIdeal Z).subschemeι ≫ φ.hom :=
  subschemeMap_subschemeι _ _ _ (vanishingIdeal_le_map_vanishingIdeal _ h.le)

/-- The underlying set of the reduced induced closed subscheme on `Z` is `Z`. -/
lemma range_vanishingIdeal_subschemeι (Z : Closeds X) :
    Set.range (vanishingIdeal Z).subschemeι.base = Z := by
  rw [range_subschemeι, coe_support_vanishingIdeal]

end AlgebraicGeometry.Scheme.IdealSheafData
