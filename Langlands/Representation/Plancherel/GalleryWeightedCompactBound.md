# Weighted compact tensor bound

For the ordered triple `y, θ, x`, the inverse of the normalized comparison
from `y` to `θ` preserves the product of the two fixed compact norms. The
continued composition along the triple has its prescribed Haar factor. A
uniform bound for the inverse of the outer forward operator, together with
the weighted round-trip identity, bounds the weighted tensor on each pure
input. Addition extends the estimate to any fixed tensor. The polynomial
numerator then satisfies the cleared bound on the entire unitary parameter
group by continuity. This implements the norm argument of Waldspurger,
*La formule de Plancherel pour les groupes p-adiques*, V.2.2 and V.3.1.

`galleryWeightedNumerator` multiplies the tensor of two continued numerator
operators by the numerator of a regular scalar ratio. The primal factor
maps from `θ` to `x`. The dual factor maps from `θ` to `y` at the inverse
parameter and is the reverse continuation in the generic comparison from
`y` to `θ`. `galleryWeightedDenominator` multiplies the scalar denominator
and these two operator denominators, with the dual denominator evaluated
at the inverse parameter. The polynomiality proof uses finite regular
expansions, tensoring and parameter inversion.

The cleared estimate uses the given compact Iwasawa factorizations, the
square-integrable inducing representation with its central quotient Haar
measure, a fixed invariant positive inducing form, and generic comparison
data for the two ordered pairs. On the supplied dense unitary subset,
the continuations are regular and their scalar-weighted round trip is
constant. `exists_compactContinuationValue_comp_smul` accounts for the
positive quotient measure factor in the distance-additive triple. The
result bounds each vector in the fixed compact tensor in the norm of the
tensor of the two probability models. Its assumptions specify the
ambient part of the scalar and operator comparison in V.2.2.
