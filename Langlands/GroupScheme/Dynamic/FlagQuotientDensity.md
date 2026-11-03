# Rational lifting from density and an identity-coset section

This internal adapter works with an actual group scheme `G` over a field `k`,
an actual subgroup functor `H`, one relative scheme `Q`, and a morphism
`q : G.X ⟶ Q`. It retains quasi-compactness, flatness and surjectivity of
`q.left`, and the exact right-coset fiber equivalence on every relative test
scheme. The universe is arbitrary. The generic results require the union of
the images of the actual rational group points to be Zariski dense, and one
actual section `s` of `q` over an open `U` containing the whole image of the
identity coset.

`flagQuotientOrbitHom` constructs the orbit morphism of an arbitrary rational
quotient point using the single scheme action from `FlagQuotientAction`.
`comp_flagQuotientOrbitHom` identifies precomposition with evaluation on every
test scheme. To prove `flagQuotientOrbit_preimage_nonempty`, the implementation
forms the actual pullback of `q.left` along the rational point. Its projection
is surjective, so its scheme has a point over the closed point of `Spec k`.
The second projection gives a local group lift. The inverse of this lift sends
the original quotient point to the identity coset, by the action lift formula
and group cancellation. Evaluating this equality at the chosen pullback point
exhibits a point in the inverse image of `U` under the orbit morphism.

`rational_lifts_of_dense_identity_section` intersects that nonempty open
preimage with the dense union of rational group-point images. Since the prime
spectrum of a field has one point, the resulting rational orbit point has its
whole image in `U`. The actual open-immersion factorization and `s` lift that
translated quotient point to `G`. Multiplying the lift by the inverse of the
chosen rational group point, and applying the action's inverse-cancellation
law, lifts the original point. The implementation transports between the
published `RationalPoint` and `RingPoint` conventions using
`rationalPointEquiv` and its naturality law.

`rational_lifts_of_reductive_density` specializes the generic argument to an
infinite field and a connected reductive group, taking the existing
`ReductiveRationalPointDensityStatement` as an explicit input.
`localSections_of_dense_identity_section` applies the published rational-lift
section-translation adapter to obtain algebraic sections near every rational
point of this same `Q`.

The provenance is internal: these are categorical, topological and group-law
consequences of the displayed inputs and the published point and translation
constructions. No external theorem is used to discharge the density input.
This unit constructs neither the quotient nor its identity-neighborhood
section, and supplies no finite-field lifting theorem. The unconditional
density proof and the full `DynamicFlagQuotientExistenceStatement` remain
separate obligations.
