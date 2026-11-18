# A uniform bound for the actual opposite scalar's inverse

This internal consequence of the actual opposite-intertwiner constructions
proves a uniform estimate needed in the inverse-regularity branch. Its
dependencies are the derived square-integrable coefficient form, the adjunction
with a positively scaled auxiliary source pairing, the uniform forward test
section, and `ContinuedScalarNormBound`. The actual scalar and the original
intertwining measures retain their normalization.

`UnitaryCommonRegularInverseBounded` says that one positive real constant bounds
the inverse rational scalar's complex value at every unitary parameter where
both supplied continuations are regular. Each bounded value is witnessed by a
fraction whose denominator is nonzero at that parameter.

`unitaryCommonRegularInverseBounded_of_admissible_unitary` proves this property
for the actual conditional canonical rational scalar, starting with an
admissible coefficient representation and an invariant positive form.
`unitaryCommonRegularInverseBounded_of_squareIntegrable` derives these data from
the original square-integrability modulo a central subgroup and nonempty
irreducibility-locus hypotheses. The subgroup need not be closed. The theorem
does not need the original target's additional finite norm-kernel quotient
assumption, so it applies in particular when that assumption is supplied.
The two open nonempty convergence regions, the open nonempty irreducibility
locus, and the actual forward and reverse continuations are retained.

For a nonzero coefficient vector `v`, the uniform test section `e` has continued
forward evaluation at the identity equal to `c • v` throughout the whole
forward regular region, with `c ≠ 0`. Compose this evaluation with the
coefficient functional `b(v, -)`. Its value on the continued family is the
constant nonzero number `c * b(v, v)`. The finite polynomial numerator span
therefore gives a uniform bound for the inverse target quadratic coefficient.
The conjugate reverse domain follows from admissibility and coefficient
unitarity. Continued adjunction with the positive auxiliary source pairing
identifies the actual scalar value with the target diagonal divided by the
fixed nonzero source diagonal on `e`. The generic bound then applies at every
unitary common regular parameter.

The field and representation carrier have independent universes, and the
field is any nonarchimedean local field, including positive characteristic.
The ambient connected reductive group and the compact open subgroup satisfying
the two Iwasawa decompositions are arbitrary. No compact Levi splitting,
conjugate-domain inclusion, coefficient unitarizability, or analytic estimate
is added as a final hypothesis of the square-integrable theorem.

This proves an estimate on the common regular locus. It does not prove
algebraic regularity at all unitary parameters and does not by itself establish
`ConditionalDynamicOppositeUnitaryScalarStatement`.
