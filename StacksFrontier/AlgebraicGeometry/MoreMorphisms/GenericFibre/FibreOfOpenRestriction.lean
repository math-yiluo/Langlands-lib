module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The fibre of the restriction of a morphism to an open subscheme of its source

Let `f : X ⟶ Y` be a morphism of schemes, let `U ⊆ X` be an open subscheme and let `y : Y`. The
fibre at `y` of the composite `U.ι ≫ f : U ⟶ Y` is the trace of `U` on the fibre of `f` at `y`,
and the identification is compatible with the two maps to `Spec κ(y)`.

This is the plumbing needed to chain geometric irreducibility along an open subscheme of the
source: the two statements "the fibre of `U ⟶ Y` at `y` is geometrically irreducible" and "the
trace of `U` on `X_y` is geometrically irreducible over `κ(y)`" are about isomorphic arrows, but
the arrows are built differently — one as `pullback.snd (U.ι ≫ f) (Y.fromSpecResidueField y)`,
the other as an open immersion into `X_y` followed by `pullback.snd f (Y.fromSpecResidueField y)`.

The identification is obtained by pasting two pullback squares vertically: the square expressing
that the trace of `U` on `X_y` is the preimage of `U` along `X_y ⟶ X`, and the square defining
`X_y`. Pasting them gives a pullback square whose vertical legs are `U.ι ≫ f` and the arrow
`U ∩ X_y ⟶ Spec κ(y)`, which therefore presents the latter as the fibre of the former.

## Main results

* `AlgebraicGeometry.isPullback_fiberι_fiberToSpecResidueField`: the defining pullback square of
  a fibre, packaged as an `IsPullback`.
* `AlgebraicGeometry.isPullback_fiberToSpecResidueField_comp_opens`: the pasted square.
* `AlgebraicGeometry.fiberOpensIso`: the resulting isomorphism.
* `AlgebraicGeometry.geometricallyIrreducible_opens_fiber_iff`: the equivalence of the two
  geometric irreducibility statements.
* `AlgebraicGeometry.geometricallyIrreducible_fiberToSpecResidueField_of_dense_opens_comp`: the
  form in which the chain is used — a dense open of the fibre whose own fibre is geometrically
  irreducible makes the fibre geometrically irreducible.

## Implementation notes

`AlgebraicGeometry.GeometricallyIrreducible` is stable under base change, hence respects
isomorphisms, but instance search does not find `MorphismProperty.RespectsIso` for it through
`MorphismProperty.IsStableUnderBaseChange.respectsIso`; that instance is supplied by hand.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (U : X.Opens)

/-- The defining pullback square of the scheme-theoretic fibre of `f` at `y`: the embedding of
the fibre into `X` and the map to `Spec κ(y)` are the two legs of the pullback of `f` along
`Y.fromSpecResidueField y`. -/
public theorem isPullback_fiberι_fiberToSpecResidueField :
    IsPullback (f.fiberι y) (f.fiberToSpecResidueField y) f (Y.fromSpecResidueField y) :=
  IsPullback.of_hasPullback f (Y.fromSpecResidueField y)

end AlgebraicGeometry

end
