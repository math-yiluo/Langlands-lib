# Algebraic and separable completed residues of finite degree

This internal module treats an actual spectrum point of a normed algebra over a
complete ultrametric normed field `K`. The base field may have trivial norm, and
the algebra and field universes are independent.

## The algebraic quotient

If `CompletedResidueField K y` is finite over `K`,
`surjective_completedResidueMap_of_finite` proves that the canonical character
from the original algebra `B` onto that completed residue field is surjective.
Its image is a `K`-subalgebra of a finite-dimensional vector space, hence finite
over `K` and closed. The published finite-subalgebra density theorem then shows
that this image is the entire completed residue field.

`completedResidueQuotientEquivOfFinite` identifies `B ⧸ y.kernel` with the
completed residue field as a `K`-algebra. The kernel of the canonical character
equals the seminorm kernel by the character's norm formula. The equivalence is
the induced quotient equivalence followed by the first isomorphism theorem.
Thus finite residue degree implies that completion adds no new values to the
image of `B`.

## Separability over a base-field character

Consider a bounded map `f : A → B` of finite type, unramified at `y` in the
published pointwise sense. Suppose a `K`-algebra character `g : A → K`
realizes the restriction of `y`. Suppose also that the completed residue field
of `y` is finite over `K`.

`isSeparable_completedResidue_of_unramified_over_baseFieldCharacter` proves
that this completed residue extension over `K` is separable.

The isometric completed-residue lift for `g` identifies each canonical image of
`a` with the scalar `g a`. Compatibility with completed-residue comap therefore
shows that the composite `A → B → H(y)` factors through `g : A → K`. These
maps provide the two scalar towers needed below.

Pointwise unramifiedness for a map of finite type means that `B` localized at
the prime `y.kernel` is formally unramified over `A`. The canonical character
`B → H(y)` extends to that localization: elements outside the seminorm kernel
have nonzero image and hence are units in `H(y)`. The extension is surjective
by the preceding canonical-character theorem. Formal unramifiedness passes
to this quotient and then from `A` to the intermediate scalar field `K`.
The published field theorem identifies formal unramifiedness of the finite
field extension with separability.

The theorem retains finite residue degree as an explicit hypothesis. It does
not construct a Galois closure, prove invariance of an algebraic point, or
perform algebraic-space descent.

## Provenance

This is an internal deduction from the published canonical completed-residue
map, lift, comap and their norm formulas; the finite-subalgebra closure and
density results; the existing pointwise unramifiedness comparison; and
Mathlib's localization, formal-unramifiedness and field-separability APIs.
No new geometric or unproved statement is assumed.
