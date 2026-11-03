# Exact subgroup inverse images in quotient squares

Author: Worker 1369.

This internal derived unit works over an arbitrary base scheme in universe
`u`. Let `i : B → G`, `q : G → Q`, `qB : B → BQ` and `iQ : BQ → Q` be actual
group-scheme homomorphisms. Assume that the underlying relative morphism of
`i` is monic, that `qB` is flat, surjective and quasi-compact, that
`i ≫ q = qB ≫ iQ`, and that the actual kernel range of `q` is contained in
`range i`.

`comap_range_eq_of_fpqc_square` proves
`(range iQ).comap q = range i` on every original scheme test. It requires no
surjectivity on points of an arbitrary test scheme. It also requires no
field, smoothness, centrality, representability of a quotient sheaf, or
monicity of `iQ`.

For a test scheme `T`, an ambient point `x` in the left side has a point
`y : T → BQ` whose image in `Q` is `q(x)`. Pull back `qB` along `y`. Over
this fpqc cover, `y` lifts to `b : V → B`. The commuting square gives equal
quotient images of the restrictions of `x` and `i(b)`. Their right
difference lies in the actual kernel of `q`, hence in `range i`. Since
`i(b)` is also in this subgroup, the restriction of `x` belongs to it.
The published `mem_range_of_comp_mem_range` descends that factorization
through the monomorphism `i`. The reverse containment follows directly
from the commuting square.

`quotientPreimagePoint` chooses the resulting actual morphism `T → B`.
`quotientPreimagePoint_comp` proves that its composite with `i` is exactly
the original point.

The provenance is the existing scheme-theoretic kernel criterion,
point-group laws and fpqc factorization descent. This supplies the
inverse-image step for a constructed central quotient square in Borel
normalizer induction. Construction of either quotient and descent of the
Borel property remain separate obligations.
