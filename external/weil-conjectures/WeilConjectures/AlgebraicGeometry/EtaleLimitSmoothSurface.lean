/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Étale limits of smooth surfaces

The local calculation of the trace formula (blueprint
`lemma-cohomology-near-two-transverse-divisors`, `lemma-vanishing-restrictions-after-blowing-up--1`)
works on schemes `Z` over a field `k` that are "a regular smooth surface over `k`, or an étale limit
with affine transition maps of such surfaces", such as the strict localization of a smooth surface
at a point, or an open subscheme of its blow-up.

## Main definitions

- `AlgebraicGeometry.IsEtaleLimitOfSmoothSurfaces Z`: the `k`-scheme `Z` is the limit of a
  cofiltered diagram of smooth `k`-schemes of relative dimension `2` whose transition maps are
  affine and étale. A smooth surface itself is the limit of the one-object diagram
  (`AlgebraicGeometry.IsEtaleLimitOfSmoothSurfaces.of_smoothOfRelativeDimension`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- A `k`-scheme `Z` is an *étale limit of smooth surfaces* if it is the limit of a cofiltered
diagram of smooth `k`-schemes of relative dimension `2` with affine étale transition maps
(blueprint `lemma-cohomology-near-two-transverse-divisors`: "a regular smooth surface over `k`, or
an étale limit with affine transition maps of such surfaces"; smooth schemes over a field are
regular). -/
def IsEtaleLimitOfSmoothSurfaces (Z : Over (Spec (.of k))) : Prop :=
  ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (F : J ⥤ Over (Spec (.of k)))
    (c : Cone F), Nonempty (IsLimit c) ∧ Nonempty (c.pt ≅ Z) ∧
    (∀ j, SmoothOfRelativeDimension 2 (F.obj j).hom) ∧
    ∀ ⦃i j : J⦄ (f : i ⟶ j), IsAffineHom (F.map f).left ∧ Etale (F.map f).left

/-- A smooth `k`-scheme of relative dimension `2` is an étale limit of smooth surfaces, as the
limit of the one-object diagram. -/
lemma IsEtaleLimitOfSmoothSurfaces.of_smoothOfRelativeDimension (Z : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 2 Z.hom] : IsEtaleLimitOfSmoothSurfaces Z := by
  refine ⟨PUnit, inferInstance, inferInstance, (Functor.const _).obj Z,
    (Cone.mk Z { app := fun _ ↦ 𝟙 Z }), ⟨?_⟩, ⟨Iso.refl _⟩,
    fun _ ↦ ‹SmoothOfRelativeDimension 2 Z.hom›,
    fun _ _ _ ↦ ⟨?_, ?_⟩⟩
  · exact
      { lift s := s.π.app PUnit.unit
        fac s j := by cases j; simp
        uniq s m hm := by simpa using hm PUnit.unit }
  · change IsAffineHom (𝟙 Z.left)
    infer_instance
  · change Etale (𝟙 Z.left)
    infer_instance

/-- Being an étale limit of smooth surfaces is invariant under isomorphism. -/
lemma IsEtaleLimitOfSmoothSurfaces.of_iso {Z Z' : Over (Spec (.of k))} (e : Z ≅ Z')
    (h : IsEtaleLimitOfSmoothSurfaces Z) : IsEtaleLimitOfSmoothSurfaces Z' := by
  obtain ⟨J, _, _, F, c, hc, ⟨e'⟩, hs, ht⟩ := h
  exact ⟨J, _, ‹_›, F, c, hc, ⟨e' ≪≫ e⟩, hs, ht⟩

end AlgebraicGeometry
