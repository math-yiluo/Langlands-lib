# Rational contracting subgroups under a central isogeny

Author: Worker 1631.

This internal construction restricts the actual point map of a group-scheme
homomorphism `q : C → G` to the dynamic subgroups associated to a supplied
cocharacter `χ : Gm → C` and its composite `χ ≫ q`. The definition
`Dynamic.unipotentPointsMap q χ T` is this restriction over every test scheme
`T` over the base scheme.

When `C` is separated over the base and the full scheme-theoretic kernel of
`q` is central, this restriction is injective on every test scheme. Indeed,
a contracting point in the kernel is central, so its conjugation orbit is
constant. Its limit is therefore both itself and the identity. Uniqueness
of orbit limits in a separated group forces it to be the identity.

Over an arbitrary field `k`, suppose that the underlying schemes of `C`
and `G` are separated and `q` is a central isogeny in the Library's
finite, flat, surjective convention, including local finite presentation.
Then `centralIsogenyUnipotentPointsEquiv q hq χ` is an isomorphism between
the groups of rational points in `U_C(χ)` and `U_G(χ ≫ q)`. Its underlying
map is composition with `q` itself.

For surjectivity, the published rational contracting-point lifting theorem
first gives an ambient rational lift `g'` of a target contracting point.
Properness of `q` extends the source conjugation orbit of `g'` across zero,
since its image has the prescribed target orbit extension. The limit `l`
of this extension maps to the identity and hence is central. Thus
`g' * l⁻¹` contracts to the identity and still maps to the original target
point. Together with the injectivity above, this proves the asserted
multiplicative equivalence. No surjectivity on the entire ambient rational
point group is asserted.

The provenance is derived: the construction uses the Library's actual
dynamic subgroups, central-kernel predicate, rational contracting-point
lift, proper affine-line extension and uniqueness of orbit limits. It
requires no reductivity, perfectness or smoothness of the central kernel.
It is a prerequisite for comparisons under central covers. It does not
construct a torus comparison, identify individual relative root groups,
transport root-datum valuations or assert apartment axioms for a cover.
