/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.Compactification.RefinementPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Morphisms out of a dense compactification

Source: blueprint main-20261015, chap-Nagata-compactification-and-Chows-lemma,
`proposition-dense-compactifications-form-cofiltered-category--2` (blueprint:
proposition-dense-compactifications-form-cofiltered-category--2).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism from a dense compactification to a compactification is proper, preserves
exactly the distinguished open, and is unique among morphisms satisfying the two
commuting triangles. Source: blueprint main-20261015, chap-Nagata-compactification-and-Chows-lemma,
`proposition-dense-compactifications-form-cofiltered-category--2` (blueprint:
proposition-dense-compactifications-form-cofiltered-category--2).

Proof: bundle the two triangles as an upstream refinement, whose ambient map is
proper. The existing dense-refinement pullback theorem identifies its square over
`X` as cartesian; the image/preimage identity for this square, applied to the whole
of `X`, gives equality of the distinguished opens. Finally, separated-target
rigidity applied after the scheme-theoretically dominant source open proves uniqueness. -/
theorem denseCompactification_refinement_morphisms {X S : Scheme.{u}} {f : X ⟶ S}
    (c' c : Compactification.QuasiCompactObjects f)
    (hc' : IsSchemeTheoreticallyDominant c'.obj.i)
    (h : c'.obj.Z ⟶ c.obj.Z)
    (hS : h ≫ c.obj.g = c'.obj.g)
    (hj : c'.obj.i ≫ h = c.obj.i) :
    IsProper h ∧
      Compactification.boundaryRefinementProperty f
        (ObjectProperty.homMk (X := c') (Y := c) ⟨h, hj, hS⟩) ∧
      ∀ (h' : c'.obj.Z ⟶ c.obj.Z),
        h' ≫ c.obj.g = c'.obj.g → c'.obj.i ≫ h' = c.obj.i → h' = h := by
  have : QuasiCompact c'.obj.i := c'.property
  have := hc'
  let r : c'.obj.Refinement c.obj := ⟨h, hj, hS⟩
  refine ⟨r.isProper, ?_, ?_⟩
  · have hp := r.isPullback_of_isSchemeTheoreticallyDominant
    change h ⁻¹ᵁ c.obj.i.opensRange = c'.obj.i.opensRange
    apply TopologicalSpace.Opens.ext
    have he := Scheme.image_preimage_eq_of_isPullback hp.flip (Set.univ : Set X)
    simpa using he.symm
  · intro h' h'S h'j
    exact ext_of_isSchemeTheoreticallyDominant_of_isSeparated c.obj.g
      (h'S.trans hS.symm) c'.obj.i (h'j.trans hj.symm)

end AlgebraicGeometry
