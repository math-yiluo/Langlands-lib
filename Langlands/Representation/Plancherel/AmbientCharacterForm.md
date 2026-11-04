# Local character forms induced from a single ambient positive form

This internal construction starts with one specified positive symmetric real
bilinear form on the full real character space of an actual split torus `T`.
For an actual monomorphism `f : A → T` of split tori, it constructs a real
linear lift of actual character restriction and an induced local form.
It proves the `CompatibleCharacterForms` condition for these constructions.
No representation-theoretic or analytic assertion is assumed or concluded.

The initial linear algebra is stated for a finite-dimensional real vector
space `V`, an arbitrary real vector space `W`, a surjective real linear
map `q : V → W`, and a specified symmetric form `B` with `B x x > 0` for
each nonzero `x`. The restriction of `B` to `ker q` is nondegenerate:
either separation condition follows by testing the vector against itself.
Mathlib's orthogonal-complement theorem then splits `V` as `ker q` and
its right orthogonal complement. Symmetry allows interchange of the two
arguments whenever an orthogonality equality is used.

`orthogonalRestrictionEquiv` restricts `q` to this orthogonal complement.
It is injective by disjointness from `ker q` and surjective by decomposing
an arbitrary lift as a kernel vector plus an orthogonal vector.
`orthogonalLift` is the inverse equivalence followed by the subtype
inclusion. Its restriction is the identity, and its image is orthogonal
to `ker q`. `quotientForm` is the pullback of `B` along this lift in both
arguments. It is symmetric and strictly positive on nonzero vectors,
since the lift is injective.

`pairing_orthogonalLift` proves
`B (L x) y = quotientForm x (q y)`. The difference `y - L (q y)` is in
`ker q`, so it pairs to zero with `L x`; symmetry puts the equality in
the required argument order. Expanding this difference yields the identity.
This proof constructs the form comparison instead of assuming it.

The final constructions use the Library's full actual character lattices
and their real scalar extensions. Actual splitness of `T` supplies the
finite-dimensional ambient space. The published
`IsSplitTorus.rationalCharacterRestrictReal_surjective_of_mono` proves
surjectivity of the actual restriction map from splitness of `A` and `T`
and the monomorphism of the underlying scheme map. Thus
`characterRestrictionOrthogonalLift` and `inducedCharacterForm` need no
additional surjectivity premise. The section law, symmetry and positivity
are proved for these actual constructions.
`inducedCharacterForm_compatible` supplies the exact
`CompatibleCharacterForms f (inducedCharacterForm ...) B
(characterRestrictionOrthogonalLift ...)` proposition.

The field has arbitrary universe and characteristic; rank zero and central
character directions are retained. The ambient form remains an explicit
input. The construction does not identify the induced local form with an
independently chosen form, prove Weyl invariance under unspecified local
actions, identify a split component of an unspecified Levi, realize a real
parameter by an unramified character, or prove convergence or rationality
of intertwining operators. The provenance is finite-dimensional linear
algebra and the published actual split-torus restriction theorem.
