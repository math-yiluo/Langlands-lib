# Rational Bruhat double-coset reduction

This internal reduction uses the published actual group-scheme constructions
from `Rational.Statement` and Mathlib's double-coset quotient. Its provenance is
the elementary quotient step in the rational Bruhat formulation: the
whole-torus centralizer lies in every dynamic parabolic associated to a
cocharacter through that torus. It does not supply the geometric covering or
separation theorem for connected reductive groups.

`centralizerPoints_le_dynamicParabolic` holds over any base scheme. It applies
the published inclusion from the whole-torus centralizer into the dynamic
centralizer, followed by the published inclusion of the latter into the
dynamic parabolic, and identifies its base points with `centralizerPoints`.

Over any field, `relativeWeyl_eq_iff_inv_mul_mem_centralizerPoints` rewrites
equality in the actual relative Weyl quotient as centralizer membership of
`n⁻¹ * n'`. `exists_parabolic_mul_of_relativeWeyl_eq` then expresses `n'` as
`1 * n * (n⁻¹ * n')`. Neither result assumes maximality, genericity,
reductivity, or a statement about surjectivity on rational points.

`rationalBruhatDoubleCosets i ν` is Mathlib's double-coset quotient of the
actual rational-point group by the dynamic parabolic on both sides.
`relativeWeylToDoubleCosets i ν` sends a relative Weyl class represented by
`n` to the double coset of `n`. The preceding factorization proves that this
map is independent of the representative.

`relativeWeylToDoubleCosets_surjective_iff` identifies surjectivity with
covering by `P(k) n P(k)` for normalizing points. Finally,
`hasRationalBruhatDecomposition_iff_bijective` identifies the existing
`HasRationalBruhatDecomposition` predicate with bijectivity of this canonical
map. These proofs use quotient induction and the explicit double-coset
equality criterion. The full `RationalBruhatStatement` still requires the
geometric proof of bijectivity at its published hypotheses.
