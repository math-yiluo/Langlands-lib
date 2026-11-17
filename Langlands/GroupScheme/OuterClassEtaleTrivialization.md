# Finite carriers from an étale trivialization of the outer parameter

This internal derived module composes generic-section extension with the
finite-carrier and outer-quotient comparison constructions. All schemes, rings,
and coproduct index types lie in one arbitrary universe.

Let `R` be a commutative domain DVR, and let `K` be its specified fraction field
with its given `R`-algebra structure. Fix group schemes `G`, `H`, and `A` over
`Spec R`, a representing `GroupIsomorphismScheme G H`, and an action of `A` on
`G`. For a supplied outer quotient `O`, assume its structure morphism is
separated and supply an étale surjection `q : U ⟶ Spec R` together with an
actual isomorphism over `U` from the pullback of `O.parameter` to the coproduct
of `J` copies of `U`. The cover may be disconnected and need not be
quasi-compact; `J` may be infinite.

For every specified fraction-field point `p` of the isomorphism scheme,
`FiniteGenericOuterClass.ofEtaleTrivialization` extends the exact composite
`p ≫ O.classMap` using `sectionOfEtaleTrivialization`. Its generic-restriction
law is exactly the equation needed by `ofIntegralClass`. That constructor uses
`Spec R` with its finite identity structure morphism as the carrier, the
extended section as its map to the outer parameter, and the original
`Spec.algebraMap R K` as its generic point. Thus the carrier records the
prescribed outer class of `p`, with the original fraction-field algebra map.

`FiniteGenericOuterClass.ofComparisonEtaleTrivialization` permits a second
supplied quotient `O'` of the same representing scheme and action to carry the
separatedness and trivialization data. It constructs the carrier for `O'` and
transports it to `O` with `ofComparison`. The latter postcomposes its class map
with the canonical quotient comparison and preserves its finite relative
scheme and generic point. Its class-map identity gives precisely the class of
the same `p` in `O`. No geometric property of `O` is an additional premise.

These constructions are categorical compositions of the imported internal
results; they make no new assertion from external literature. Reductivity is
not required for the conditional constructions. The existence of a separated
outer quotient with an actual étale coproduct trivialization remains an
explicit geometric input. This module does not supply that input or prove
`FiniteGenericOuterClassExistenceStatement`. It adds no henselian, completeness,
residue-field, splitting, characteristic, or smooth-centre hypothesis.
