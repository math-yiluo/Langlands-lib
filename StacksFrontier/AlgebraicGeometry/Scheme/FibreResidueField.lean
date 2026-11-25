module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The residue field of a scheme-theoretic fibre

A morphism of schemes which is surjective on stalks induces a *surjective* map of residue
fields, and a map of fields is injective, so the induced map is an isomorphism. The projection
of a scheme-theoretic fibre to the ambient scheme is a preimmersion, hence surjective on stalks,
so the residue field of the fibre of `f : X ⟶ Y` over `y` at a point `p` agrees with the residue
field of `X` at the image of `p`. This file records that comparison in the form needed to read a
transcendence degree over the residue field of the image point off the fibre or off the ambient
scheme interchangeably.

## Main results

* `AlgebraicGeometry.trdeg_residueField_comp_of_surjectiveOnStalks`: restricting the source of a
  morphism along a morphism surjective on stalks does not change the transcendence degree of the
  residue field extension at a point.
* `AlgebraicGeometry.trdeg_residueField_fiber`: the special case of the projection of a
  scheme-theoretic fibre.

## Implementation notes

The extension is recorded as an `Algebra` instance built from
`AlgebraicGeometry.Scheme.Hom.residueFieldMap`, the convention in which the three numerical
invariants of Stacks 04NM are stated, rather than the `Scheme.ΓSpecIso`/`Scheme.Γevaluation`
convention used for a morphism to the spectrum of a literal field in
`StacksFrontier/AlgebraicGeometry/Variety/Defs/Dimension/ResidueField.lean`. The two statements are
therefore not interchangeable, and the surjectivity-of-residue-fields step is repeated here;
what is new is that the comparison is available over the residue field of the image point, which
is what a fibre of a morphism of schemes comes with.

The point of the fibre is left as an arbitrary `p`, with its image written out as
`f.fiberι y p`; a client holding the distinguished point of the fibre through `x` rewrites with
`AlgebraicGeometry.Scheme.Hom.fiberι_asFiber`.

## References

* [Stacks Project, Tag 01J9](https://stacks.math.columbia.edu/tag/01J9)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes which is surjective on stalks induces a surjective map of residue
fields. -/
public theorem surjective_residueFieldMap_of_surjectiveOnStalks {X Z : Scheme.{u}} (i : Z ⟶ X)
    [SurjectiveOnStalks i] (z : Z) : Function.Surjective (i.residueFieldMap z).hom := by
  have h := (Z.residue_surjective z).comp (i.stalkMap_surjective z)
  change Function.Surjective (i.stalkMap z ≫ Z.residue z).hom at h
  rw [← Scheme.residue_residueFieldMap i z] at h
  intro a
  obtain ⟨b, hb⟩ := h a
  exact ⟨(X.residue (i z)).hom b, hb⟩

end AlgebraicGeometry

end
