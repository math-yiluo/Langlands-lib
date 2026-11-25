/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory

/-!
# Boundary-preserving refinements of compactifications

Source: blueprint main-20261015, chap-Nagata-compactification-and-Chows-lemma,
definition-compactification-refinement, definition-compactification-refinement--3
(blueprint: definition-compactification-refinement--3).

The upstream `Compactification.Refinement` records the two commuting triangles only.
Here morphisms additionally preserve the inverse image of the distinguished open.
Objects have quasi-compact open immersions, as required in this node. Equality in
`Scheme.Opens` is equality of open subschemes, each with its restricted structure sheaf.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification

/-- Compactifications with quasi-compact open immersion, using the existing compactification
structure. Source: blueprint main-20261015, definition-compactification-refinement--3, opening
sentence (blueprint: definition-compactification-refinement--3). -/
abbrev QuasiCompactObjects {X S : Scheme.{u}} (f : X ⟶ S) : Type (u + 1) :=
  ObjectProperty.FullSubcategory (fun c : Compactification f ↦ QuasiCompact c.i)

/-- The third refinement condition: the inverse image of the target's distinguished open is
exactly the source's distinguished open. The underlying upstream refinement already gives
`r.hom.hom ≫ d.obj.g = c.obj.g` and `c.obj.i ≫ r.hom.hom = d.obj.i`.
The latter identifies the restriction with `j ∘ (j')⁻¹`; the additional equality says that
boundary points map to boundary points.
Source: blueprint main-20261015, definition-compactification-refinement--3, conditions 1--3
(blueprint: definition-compactification-refinement--3). -/
def boundaryRefinementProperty {X S : Scheme.{u}} (f : X ⟶ S) :
    MorphismProperty (QuasiCompactObjects f) :=
  fun c d r ↦ r.hom.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange

/-- Identity refinements preserve the open, and boundary-preserving refinements compose.
Source: blueprint main-20261015, definition-compactification-refinement--3, final paragraph
(blueprint: definition-compactification-refinement--3).

Proof: the identity has inverse image equal to the same open. For consecutive refinements
`r : c ⟶ d` and `s : d ⟶ e`, inverse image under their ambient composite is the iterated
inverse image. Substitute `s⁻¹(e.i(X)) = d.i(X)` and then
`r⁻¹(d.i(X)) = c.i(X)`. The upstream identity and composition already satisfy both triangle
equalities, with ambient maps the scheme identity and composite, respectively. -/
theorem boundaryRefinementProperty_isMultiplicative {X S : Scheme.{u}} (f : X ⟶ S) :
    (boundaryRefinementProperty f).IsMultiplicative := by
  refine { id_mem := fun c ↦ ?_, comp_mem := fun r s hr hs ↦ ?_ }
  · change (𝟙 c.obj.Z) ⁻¹ᵁ c.obj.i.opensRange = c.obj.i.opensRange
    exact Scheme.Hom.id_preimage _
  · change r.hom.hom ⁻¹ᵁ _ = _ at hr
    change s.hom.hom ⁻¹ᵁ _ = _ at hs
    change (r.hom.hom ≫ s.hom.hom) ⁻¹ᵁ _ = _
    rw [Scheme.Hom.comp_preimage, hs, hr]

attribute [instance] boundaryRefinementProperty_isMultiplicative

/-- The category of compactifications with quasi-compact open immersions and refinements
satisfying all three conditions: the two commuting triangles and equality of inverse-image
open subschemes. Identities and composition are induced by those of the ambient schemes.
Source: blueprint main-20261015, definition-compactification-refinement--3, final paragraph
(blueprint: definition-compactification-refinement--3). -/
abbrev BoundaryCompactification {X S : Scheme.{u}} (f : X ⟶ S) : Type (u + 1) :=
  WideSubcategory (boundaryRefinementProperty f)

/-- The full subcategory on the scheme-theoretically dense compactifications.
Density is precisely the dependency's `IsSchemeTheoreticallyDominant` on the open immersion;
quasi-compactness is already part of the ambient category's objects.
Source: blueprint main-20261015, definition-compactification-refinement--3, last sentence, and
definition-compactification-refinement--2
(blueprint: definition-compactification-refinement--3). -/
abbrev DenseBoundaryCompactification {X S : Scheme.{u}} (f : X ⟶ S) : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun c : BoundaryCompactification f ↦ IsSchemeTheoreticallyDominant c.obj.obj.i)

end AlgebraicGeometry.Compactification
