# Saturation of the image of a slice

For a scheme equivalence relation with projections `t` and `s`, the image of
`h = pullback.snd g t ≫ s` contains the image of `g` and is saturated under
arrows of the relation on the underlying points. Neither smoothness nor
etaleness is needed.

Reflexivity applied to `g` constructs a morphism into the pullback which
exhibits `g` as a composite through `h`, proving the image inclusion.
For forward saturation, form the pullback of `h` and `t`. Its two maps to the
relation have matching target and source, so the transitivity field constructs
a composite arrow. Its source factors through `g`, giving a map from this new
pullback back into the original slice pullback. Its composite with `h` is the
target of the second relation arrow. Mathlib's existence of points over a pair
of scheme points in a pullback now gives the desired image membership. This
uses the scheme pullback result, which accounts for residue-field extensions,
rather than identifying the underlying space with a topological fibre product.
The symmetry morphism of the relation supplies reverse saturation.

These are internal helpers for moving local slice coverage along an orbit;
all relation hypotheses are the fields of the published `AtlasRelation.IsEquivRel`.
