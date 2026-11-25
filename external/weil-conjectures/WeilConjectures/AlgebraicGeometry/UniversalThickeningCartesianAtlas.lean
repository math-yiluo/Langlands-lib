/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningCartesianAtlasCore
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Cartesian charts for glued local universal thickenings

Source: Stacks Project, More on Morphisms, proof of Lemma 37.7.1 (Tag 04F3),
paragraph beginning "Choose an affine open covering".
(blueprint: lem-weil-pbc-universal-thickening-cartesian-atlas)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The geometric part of gluing local universal thickenings: open chart maps
jointly cover a scheme over `X`, and each original source chart is their pullback.
No assertion about the global immersion's kernel or its universal property is made.

Source: Stacks Project, More on Morphisms, proof of Lemma 37.7.1 (Tag 04F3),
paragraph beginning "Choose an affine open covering".
(blueprint: lem-weil-pbc-universal-thickening-cartesian-atlas)

Proof: For each pair of source charts, take their intersection as the pullback
of their open immersions into `Z`. The first order immersions are homeomorphisms,
so each intersection has a unique corresponding open in each thickened chart.
The open-pieces theorem, with the whole base open, says that these two restricted
charts are universal thickenings of the intersection over `X`. Universal uniqueness
therefore gives an isomorphism of the two thickened overlaps, over `X` and fixing
that intersection. On triple intersections the direct transition and the composite
transition extend the same identity over `X`; uniqueness makes them equal.
The same argument gives identity transitions and inverse transitions. These opens,
transition maps and cocycle identities form scheme glue data. Take its glued scheme
`W` and canonical open immersions `e k`; they jointly cover `W`. The local structure
maps agree on overlaps and glue to `p`. The maps `i k ≫ e k` agree on the source
intersections, hence glue on `C` to `j`. Checking on `C` gives `j ≫ p = h`.
Finally, in any source chart, membership in the inverse image of `e k` is exactly
membership in the prescribed thickened overlap: the gluing equivalence identifies
precisely those overlaps. Pulling back along the local first order homeomorphism
identifies this with the source intersection. The local maps and these overlap
identifications show that the square with top map `i k`, left map `C.f k`,
right map `e k` and bottom map `j` is cartesian. This also works for the empty
source cover: all thickened charts and the glued scheme are empty. -/
theorem universalFirstOrderThickening_cartesianAtlas
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (H : ∀ k, IsUniversalFirstOrderThickening (C.f k ≫ h) (i k) (h' k)) :
    ∃ (W : Scheme.{u}) (j : Z ⟶ W) (p : W ⟶ X) (e : ∀ k, Z' k ⟶ W),
      (∀ k, IsOpenImmersion (e k)) ∧ (∀ w : W, ∃ k z, e k z = w) ∧
      j ≫ p = h ∧ (∀ k, e k ≫ p = h' k) ∧
      ∀ k, IsPullback (i k) (C.f k) (e k) j := by
  obtain ⟨W, e, he, hc, hh, hi, ho⟩ :=
    universalFirstOrderThickening_cartesianAtlas_core h C Z' i h' H
  let : ∀ k, IsOpenImmersion (e k) := he
  let D : W.OpenCover.{u} :=
    { I₀ := C.I₀
      X := Z'
      f := e
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hc, he⟩ }
  let p : W ⟶ X := D.glueMorphisms h' hh
  let j : Z ⟶ W := C.glueMorphisms (fun k ↦ i k ≫ e k) hi
  have hep (k) : e k ≫ p = h' k := D.ι_glueMorphisms h' hh k
  have hij (k) : C.f k ≫ j = i k ≫ e k :=
    C.ι_glueMorphisms (fun k ↦ i k ≫ e k) hi k
  refine ⟨W, j, p, e, he, hc, ?_, hep, ?_⟩
  · apply C.hom_ext
    intro k
    rw [← Category.assoc, hij, Category.assoc, hep, (H k).2.1]
  · intro k
    apply IsOpenImmersion.isPullback (i k) (C.f k) (e k) j (hij k)
    ext z
    obtain ⟨l, z, rfl⟩ := C.exists_eq z
    have hjz : j (C.f l z) = e l (i l z) := by
      exact congrArg (fun f : C.X l ⟶ W ↦ f z) (hij l)
    change j (C.f l z) ∈ Set.range (e k) ↔ C.f l z ∈ Set.range (C.f k)
    rw [hjz]
    exact ho k l z

end AlgebraicGeometry
