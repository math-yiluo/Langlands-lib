/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine images away from the other member of a closed cover

Source: Stacks Project, Varieties, Lemma 09NX, final paragraph.
(blueprint: lem-sc-affine-image-away-closed-cover).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An affine open in one member of a closed cover, disjoint from the other member,
has affine open image in the reduced ambient scheme.

Source: Stacks Project, Varieties, Lemma 09NX, final paragraph.
(blueprint: lem-sc-affine-image-away-closed-cover).

Proof: let W be the complement of T. Restrict f to W. This is a closed immersion
surjective onto W, since the two closed subsets cover X. W is reduced, so the
restricted closed immersion is an isomorphism. As V avoids T, V is contained in
the preimage of W; the composite V -> f^-1 W -> W -> X is therefore an open
immersion. Its source is affine. Its open image is the desired affine open U,
and its set of points is f(V). Empty V and empty W cause no exception. -/
theorem exists_affineOpen_image_away_closed_cover
    {X Y : Scheme.{u}} [IsReduced X] (f : Y ⟶ X) [IsClosedImmersion f]
    (T : TopologicalSpace.Closeds X) (hcover : Set.range f ∪ (T : Set X) = Set.univ)
    (V : Y.Opens) (hV : IsAffineOpen V)
    (havoid : Disjoint (f '' (V : Set Y)) (T : Set X)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ (U : Set X) = f '' (V : Set Y)  := by
  let W : X.Opens := ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩
  have hsurj : Surjective (f ∣_ W) := by
    rw [surjective_iff]
    intro z
    have hz : z.1 ∈ Set.range f ∪ (T : Set X) := by rw [hcover]; trivial
    obtain hz | hz := hz
    · obtain ⟨y, hy⟩ := hz
      refine ⟨⟨y, ?_⟩, ?_⟩
      · change f y ∈ W
        rw [hy]
        exact z.property
      · apply Subtype.ext
        exact (morphismRestrict_base_coe f W _).trans hy
    · exact (z.property hz).elim
  let := hsurj
  have : IsAffine V.toScheme := hV
  have : IsIso (f ∣_ W) := isIso_of_isClosedImmersion_of_surjective (f ∣_ W)
  have hVW : V ≤ f ⁻¹ᵁ W := by
    intro y hy
    exact fun hz ↦ Set.disjoint_left.mp havoid ⟨y, hy, rfl⟩ hz
  let g : V.toScheme ⟶ X := Y.homOfLE hVW ≫ f ∣_ W ≫ W.ι
  have : IsOpenImmersion g := inferInstance
  have hg : g = V.ι ≫ f := by simp [g]
  refine ⟨g ''ᵁ ⊤, ?_, ?_⟩
  · exact (isAffineOpen_top V.toScheme).image_of_isOpenImmersion g
  · change g '' (Set.univ : Set V.toScheme) = f '' (V : Set Y)
    rw [hg]
    rw [Set.image_univ]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩


end AlgebraicGeometry.Scheme
