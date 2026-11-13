# Cocycle twists on the actual maximal-unramified building

This internal specialization applies `SemilinearCocycleAction.action` to the
coefficient action of `MaximalUnramified.SemilinearApartmentData`. The declaration
`twistedAction` is a group homomorphism into permutations of the original reduced
building. Its formula is exactly `y ↦ c σ • A.action σ y`, for the original
rational-point action and a cocycle for `rationalConjugate`.

`finite_twisted_orbit_of_fixed` uses the generic finite-range theorem: if the
cocycle is trivial on the fixing subgroup of a finite-dimensional intermediate
field, a coefficient-fixed point has finite twisted orbit.

`UnramifiedBuildingDescent.exists_finite_twisted_orbit` provides such an orbit for
the exact building data and coefficient action in
`UnramifiedTwistedChamberStatement`. It uses the published theorem
`unramifiedGaloisFixedApartment` to choose a coefficient-fixed apartment point,
then equivariance of the apartment map to obtain a coefficient-fixed building
point. The finite-range result finishes the proof.

These are derived implementation lemmas. They add no metric or special-fibre
assumptions, and assert neither a common fixed point nor a stable chamber.
Geometrically they implement the finite-orbit input to the fixed-point route
suggested by the correction to Kaletha–Prasad §9.2.1 (corrections dated
1 November 2024, p. 39). The finite-orbit proof here uses a fixed apartment point
and the cocycle's finite range.
