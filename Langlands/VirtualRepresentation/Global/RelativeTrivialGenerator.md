# The trivial relative Weil representation and the actual constant cusp line

This internal construction supports the rank-one clause of
`RelativeIsometryOperationStatement`. It constructs the actual trivial relative
Weil line in an independent carrier universe and compares it with the actual
constant cuspidal spectral presentation. The final result is
`Langlands.VirtualRepresentation.RelativeGlobal.trivialWitnessedGenerator`.

`RelativeLocalMapFamily` explicitly supplies a reciprocity candidate and a
characterized local-to-relative Weil map for every pair of finite places. Its
existence is a separate class-field-theoretic obligation and is not asserted in
this module. The final isometry theorem must discharge that obligation from its
published hypotheses.

The trivial line is continuous, irreducible, unitary and of rank one. Every local
restriction remains trivial. Its inertia action is identity, and its whole-carrier
Euler polynomial is `1 - X`, computed by the determinant of `1 - z` on a
one-dimensional carrier. This equals the Euler polynomial of the constructed
constant rank-one spectral presentation. Supplied local-map data therefore
establish weak association at every finite place.

The Weil lattice element is the generator of the actual unitary trivial local
line. `LocalWeil.realizeExact_ofRepresentation` and
`ExactGrothendieckGroup.ofRepresentation_eq_of_equiv` prove that it expands the
entire local restriction in the exact Grothendieck group. The comparison with
`rankOneWeilCharacterClass e 1` holds for every reciprocity candidate `e`, since
the trivial character remains trivial under pullback.

On the automorphic side, the constructed local component is equivariantly
isomorphic to `Correspondence.rankOneSupercuspidalObject 1`. This comparison
passes through the actual tensor factor, with independent lifts in the Weil,
tensor and form-carrier universes. The ordinary positive form on complex scalars
proves unitarity. The public theorem
`Classification.TwoSupercuspidalTopDerivatives.supercuspidal_singleton_support`
gives an actual normalized-induction support witness for the trivial
supercuspidal object. `IsUnitaryLatticeSupport.of_iso` transports it to the actual
constant local component. Its ambient lattice inclusion is exactly the
generator of `Correspondence.rankOneSupercuspidalClass 1`.

`trivialWitnessedGenerator` retains all these data, choosing a place above the
specified base place using `finitePlacesAbove_nonempty`. Its Weil,
presentation-factor and field universes are independent. The construction uses
no asserted local Langlands correspondence or globalization theorem.

The module has internal provenance: each construction is derived directly from
the existing trivial character line, actual constant realization, tensor
presentation, exact realization map and singleton support theorem. It does not
prove existence of `RelativeLocalMapFamily` or the exact final isometry theorem.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
