# Point counts for products of split unipotent subgroups

This is an internal counting lemma for the finite-field torus-envelope proof.
It is derived from group multiplication, the actual scheme-theoretic subgroup
intersection, and the published finite Ga-series point-count and Lie-dimension
lemmas in `Rational.SplitSeriesPointCount`. No new literature assertion is used.

For arbitrary groups, every fiber of the product of two homomorphism images is
in bijection with the pairs having equal images. The implemented equivalence
translates one chosen factorization by such a pair, using the inverse in the
second factor. A surjective product therefore gives the cardinal identity
`|V| |C| = |U| |V ×_U C|`. This identity uses natural-number cardinality and does
not need finiteness or injectivity hypotheses.

The scheme-points version identifies equal-image pairs with points of the
existing categorical pullback `subgroupIntersection`. It works on every scheme
test and requires neither closedness nor smoothness of the two subgroup maps.

Finally, over a finite field, if the three groups and their intersection are
smooth affine groups with finite Ga-series, the published cardinal formulas
express all four cardinalities as powers of the field size. Since this size is
at least two, equality of the powers gives equality of the sums of series
lengths. The published Lie-dimension formula identifies these lengths with
`Lie.dimension`. This proves the dimension equality; dominance or surjectivity
of the scheme multiplication is a separate geometric step.
