# Coefficient transport of canonical simple-reflection points

This internal unit proves that the canonical simple-reflection points constructed
from normalized root maps inherit compatibility of the actual root characters
and normalized unit points. The field extension and universe are arbitrary.
The compatibility premises are explicit; this unit does not construct a
compatible pinning or compatible normalized root maps.

For two actual acting tori related by an isomorphism and with the same
inclusion into the ambient group, `IsOppositeFactorPair.changeTorus`
preserves the ordered pair and its middle point. The character changes by
`characterLattice.congr`. The proof transports both negative-root memberships
using the actual root-subgroup transport square, and transports the normalizer
condition through the same torus isomorphism. Applying the inverse isomorphism
proves `isOppositeFactorPair_changeTorus_iff`.

Now supply a group and commutative acting group over `k`, their map `i`, and
a split pinning `p` of the base-changed group over `K`. Supply an actual
isomorphism `eT` from the pinned torus to the base-changed acting group, and
the equality identifying their maps into the ambient group. For two normalized
root parametrizations `x` and `y` at simple roots, require that the actual
character of `y`, expressed through `eT`, is the ordinary Galois transform
of that of `x`. Also require that `rationalConjugate` carries `x.unitPoint`
to `y.unitPoint`.

`oppositeFactorPair_rationalConjugate` first changes the torus in the
canonical pair certificate, then applies the actual coefficient transport
of ordered opposite pairs. The two compatibility equalities identify its
root and middle point with those of `y`. Changing back to the pinned torus
and applying `y.eq_oppositeFactorPair` identifies both ordered factors
with the canonical pair for `y`. Multiplicativity then proves
`reflectionRepresentative_rationalConjugate` for the actual representative
point.

`UnitPointsGaloisCompatible` records compatibility of the supplied normalized
unit-point family with a supplied permutation action on the simple-root
support. With the corresponding actual character transport law, the theorem
`canonicalSimpleReflectionRepresentatives_rationalConjugate` applies the
single-root result to every coefficient automorphism and simple root.
The conclusion concerns the actual points of the canonical representatives;
it does not identify the full structures or assert a descent datum for
their torus automorphisms.

The provenance is an internal deduction from actual torus/root-subgroup
transport, coefficient transport of ordered opposite pairs, and uniqueness
of the canonical opposite pair. No new original-literature assertion is
introduced. Neither compatibility of arbitrary supplied normalized maps nor
existence of compatible choices is inferred. The parent quotient theorem,
cross-section descent, exceptional even-type-A geometry, and rational lifting
remain separate obligations.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
