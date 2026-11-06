# Full compact-subgroup finiteness on the original finite-smooth carrier

For the actual infinite subgroup `Kinf` and actual finite open subgroup
`C`, `adelicCompactProductSubgroup` is their product image inside the
original full adelic group under the existing infinite/finite point
isomorphism. If both factors are compact then this actual subgroup is
compact, by continuity of that product map.

The original finite plot-smooth rational-function carrier has a smooth
finite adelic action. Therefore each original function has a finite
orbit under every compact open finite subgroup, by the published compact
orbit theorem. `isAdelicInfiniteFinite_iff_compactProduct` proves that
on this carrier, finiteness of the full function's `Kinf` orbit is
equivalent to finiteness under the product `Kinf × C`.

For the forward implication, take the finite set of finite-factor
translates of the function. Each translate has a finite-dimensional
infinite-subgroup orbit, because the two factor actions commute. The
finite supremum of these orbit spans contains the full product orbit,
so the product orbit span is finite dimensional. Conversely, the
infinite orbit is contained in the product orbit by adjoining the
identity finite element.

The product parametrization and the actual full subgroup have exactly
the same orbit as sets of original functions. Thus
`isAdelicInfiniteFinite_iff_actualCompactFinite` is an exact comparison
with finiteness under the actual subgroup, and shows independence from
the choice of compact open finite factor for this finiteness condition.
This supplies the full compact-subgroup finite formulation preceding
Getz--Hahn Definition 6.3.3, printed p.163 (physical PDF p.177). The
ambient functions are on the actual `G(A_F)`, as clarified by the author's
correction to Exercise 6.4. The comparison uses the orbit of the entire
function; it does not substitute separate finiteness conditions on each
finite adelic slice.

This internal derived comparison uses the published compact finite-orbit
and finite-vector constructions and the original actual point product.
It needs no scalar commutator, center action, reduction theory or
finite-volume premise. Existence and maximality of the infinite compact
subgroup are not inferred; in the source form construction they are
supplied explicitly. It does not compare the new full norm to the old
matrix slice-growth norm or identify the entire old matrix form space.

This finite-vector comparison does not identify the original finite-smooth
carrier with the algebraic tensor smooth carrier in GH (6.1); it remains
valid independently of that separate source-space comparison.
