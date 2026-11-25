/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Widesubcategory
public import WeilConjectures.Compactification.RefinementUniqueness

/-!

# Strict refinements of compactifications

In the blueprint (`definition-compactification-refinement--3`) a refinement `h : c ⟶ d` of
compactifications of `f : X ⟶ Y` is required to satisfy, besides the two commutativity
conditions of `AlgebraicGeometry.Compactification.Refinement`, the condition
`h⁻¹(d.i(X)) = c.i(X)`: the refinement maps the boundary of `c` into the boundary of `d`. We
call such refinements *strict*.

## Main definitions

- `AlgebraicGeometry.Compactification.Refinement.IsStrict`: a refinement is strict if the
  preimage of the copy of `X` in the target is the copy of `X` in the source;
- `AlgebraicGeometry.Compactification.strictRefinement`: the (multiplicative) morphism property
  of strict refinements;
- `AlgebraicGeometry.Compactification.StrictCategory`: the category of compactifications of `f`
  with strict refinements as morphisms, a wide subcategory of
  `AlgebraicGeometry.Compactification.category`.

## Main results

- `AlgebraicGeometry.Compactification.Refinement.IsStrict.id` and
  `AlgebraicGeometry.Compactification.Refinement.IsStrict.comp`: strict refinements contain the
  identities and compose;
- `AlgebraicGeometry.Compactification.preimage_opensRange_eq_of_isSchemeTheoreticallyDominant`:
  a morphism over `Y` out of a dense compactification commuting with the open immersions
  automatically pulls the copy of `X` back to the copy of `X`;
- `AlgebraicGeometry.Compactification.refinement_morphisms`: such a morphism is proper, strict
  and unique (blueprint `proposition-dense-compactifications-form-cofiltered-category--2`);
- `AlgebraicGeometry.Compactification.Refinement.isStrict_of_isSchemeTheoreticallyDominant`:
  every refinement out of a dense compactification is strict.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

namespace Refinement

variable {c d e : Compactification f}

/-- Blueprint `definition-compactification-refinement--3`: Refinement of compactifications.

A refinement `r` of `d` by `c` is *strict* if `r.hom⁻¹(d.i(X)) = c.i(X)`, i.e. the refinement
maps the boundary of `c` into the boundary of `d`. The refinements of the blueprint are the
strict refinements in this sense. -/
def IsStrict (r : c.Refinement d) : Prop :=
  r.hom ⁻¹ᵁ d.i.opensRange = c.i.opensRange

/-- The identity refinement is strict. -/
theorem IsStrict.id (c : Compactification f) : (Refinement.id c).IsStrict := by
  simp [IsStrict]

/-- Strict refinements compose. -/
theorem IsStrict.comp {r : c.Refinement d} {s : d.Refinement e} (hr : r.IsStrict)
    (hs : s.IsStrict) : (r.comp s).IsStrict := by
  rw [IsStrict, comp_hom, Scheme.Hom.comp_preimage, hs, hr]

end Refinement

variable (f) in
/-- The morphism property of strict refinements on the category of compactifications of `f`
(blueprint `definition-compactification-refinement--3`). -/
def strictRefinement : MorphismProperty (Compactification f) :=
  fun _ _ r ↦ Refinement.IsStrict r

instance : (strictRefinement f).IsMultiplicative where
  id_mem c := Refinement.IsStrict.id c
  comp_mem _ _ hr hs := Refinement.IsStrict.comp hr hs

variable (f) in
/-- Blueprint `definition-compactification-refinement--3`: the category of compactifications of `f`
whose morphisms are the strict refinements, i.e. the refinements `h` with
`h⁻¹(j(X)) = j'(X)`. It is a wide subcategory of `AlgebraicGeometry.Compactification.category`.
-/
abbrev StrictCategory : Type (u + 1) :=
  WideSubcategory (strictRefinement f)

/-- A morphism over `Y` out of a dense compactification `c` commuting with the open immersions
pulls the copy of `X` back to the copy of `X`: `h⁻¹(d.i(X)) = c.i(X)`. Indeed, over
`V = h⁻¹(d.i(X))` the morphism `h` induces a retraction `V ⟶ X` of the inclusion of `X`, which is
separated since `V` is separated over `Y`; so `X` is closed in `V`, and it is dense in `V`. -/
theorem preimage_opensRange_eq_of_isSchemeTheoreticallyDominant [QuasiCompact f]
    {c d : Compactification f} [IsSchemeTheoreticallyDominant c.i] (h : c.Z ⟶ d.Z)
    (hi : c.i ≫ h = d.i) (hg : h ≫ d.g = c.g) :
    h ⁻¹ᵁ d.i.opensRange = c.i.opensRange := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  let s : X ⟶ pullback h d.i := pullback.lift c.i (𝟙 X) (by rw [hi, Category.id_comp])
  have hs : s ≫ pullback.snd h d.i = 𝟙 X := pullback.lift_snd _ _ _
  have hsf : s ≫ pullback.fst h d.i = c.i := pullback.lift_fst _ _ _
  have : IsSeparated (pullback.snd h d.i) := by
    have : IsSeparated (pullback.snd h d.i ≫ d.i ≫ d.g) := by
      rw [← pullback.condition_assoc, hg]
      infer_instance
    exact IsSeparated.of_comp _ (d.i ≫ d.g)
  have : IsClosedImmersion s := by
    have : IsClosedImmersion (s ≫ pullback.snd h d.i) := by
      rw [hs]
      infer_instance
    exact IsClosedImmersion.of_comp s (pullback.snd h d.i)
  have : IsSchemeTheoreticallyDominant s := by
    have : IsSchemeTheoreticallyDominant (s ≫ pullback.fst h d.i) := by
      rw [hsf]
      infer_instance
    have : QuasiCompact (s ≫ pullback.fst h d.i) := by
      rw [hsf]
      infer_instance
    exact IsSchemeTheoreticallyDominant.of_comp s (pullback.fst h d.i)
  have hrange : Set.range s = Set.univ := by
    rw [← s.isClosedEmbedding.isClosed_range.closure_eq]
    exact s.denseRange.closure_eq
  ext1
  rw [← IsOpenImmersion.range_pullbackFst d.i h, Scheme.Hom.coe_opensRange, ← hsf,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange, Set.image_univ]

/-- Blueprint `proposition-dense-compactifications-form-cofiltered-category--2`: Morphisms out of a
dense compactification.

Let `c` be a dense compactification and `d` a compactification of a quasi-compact `f`, and let
`h : c.Z ⟶ d.Z` be a morphism over `Y` with `c.i ≫ h = d.i`. Then `h` is proper,
`h⁻¹(d.i(X)) = c.i(X)` (so `h` is a strict refinement), and `h` is the unique morphism over `Y`
with `c.i ≫ h = d.i`. -/
theorem refinement_morphisms [QuasiCompact f] {c d : Compactification f}
    [IsSchemeTheoreticallyDominant c.i] (h : c.Z ⟶ d.Z) (hi : c.i ≫ h = d.i)
    (hg : h ≫ d.g = c.g) :
    IsProper h ∧ h ⁻¹ᵁ d.i.opensRange = c.i.opensRange ∧
      ∀ h' : c.Z ⟶ d.Z, c.i ≫ h' = d.i → h' ≫ d.g = c.g → h' = h :=
  ⟨Refinement.isProper ⟨h, hi, hg⟩,
    preimage_opensRange_eq_of_isSchemeTheoreticallyDominant h hi hg,
    fun h' hi' hg' ↦ congrArg Refinement.hom
      (Refinement.ext_of_isSchemeTheoreticallyDominant ‹_› ⟨h', hi', hg'⟩ ⟨h, hi, hg⟩)⟩

/-- Every refinement out of a dense compactification of a quasi-compact morphism is strict
(blueprint `proposition-dense-compactifications-form-cofiltered-category--2`). -/
theorem Refinement.isStrict_of_isSchemeTheoreticallyDominant [QuasiCompact f]
    {c d : Compactification f} (hc : IsSchemeTheoreticallyDominant c.i) (r : c.Refinement d) :
    r.IsStrict :=
  preimage_opensRange_eq_of_isSchemeTheoreticallyDominant r.hom r.i_hom r.hom_g

end AlgebraicGeometry.Compactification
