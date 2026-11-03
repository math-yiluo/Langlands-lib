# Finite Galois descent of fixed-torus dynamic presentations

This internal construction descends a supplied dynamic presentation through a
fixed torus. Let `k` and `K` be fields in the same arbitrary universe `u`, with
`K/k` finite dimensional and Galois and with a finite enumeration of its
automorphism group. Let `G` be a smooth connected affine group scheme over
`k`, `T` an affine commutative group scheme over `k`, `j : T → G` a
homomorphism, and `i : P → G` a homomorphism whose underlying morphism in
`Over (Spec k)` is monic. Assume that `T_K` is a split torus.

Given an actual cocharacter `ν` of `T_K` with
`range(i_K) = Dynamic.parabolic (ν ≫ j_K)`, the definition
`fixedTorusDynamicPresentationGaloisDescend` returns an actual cocharacter of
`T` with `range(i) = Dynamic.parabolic (μ ≫ j)`. Its value is the published
`CocharacterAveraging.descendedOrbitSum k K T ν`. Thus the resulting
cocharacter is over the original field. Each equality is an equality of
subgroup functors on all test schemes.

The theorem `exists_range_eq_parabolic_iff_finiteGaloisBaseChange` expresses the
corresponding equivalence of existence before and after the specified field
extension. The torus need only split over `K`; splitness over `k`, maximality
and reductivity are not hypotheses.

## Implemented proof

The helper `FixedTorusGaloisDescent.range_eq_parabolic_descendedOrbitSum`
proves the certificate used by the construction.

1. Smoothness and affineness persist after base change.
   `GroupScheme.connectedSpace_baseChange_of_smooth_affine` supplies
   connectedness of `G_K`.
2. `fixedTorusDynamicPresentation_galois` shows that every Galois translate of
   `ν` presents the same `i_K`. Apply the published necessary criterion
   `RelativeRoot.nonnegative_rootSupport_of_parabolic_le` in both directions.
   At each actual relative root of `j_K`, nonnegativity of its integer pairing
   with every translate is equivalent to nonnegativity of its pairing with
   `ν`.
3. Apply `CocharacterAveraging.nonneg_orbitSum_iff` separately to each such
   pairing. The integral orbit sum therefore has exactly the same
   nonnegative root region as `ν`. This uses no division and no separate
   stability or negation-closure hypothesis on the root family.
4. Apply `RelativeRoot.parabolic_le_iff_nonnegative_rootSupport` in both
   directions, discharging its connectedness-statement premise with the
   published theorem `dynamicConnected`. Antisymmetry gives equality of the
   two dynamic subgroup functors over `K`.
5. `CocharacterAveraging.baseChange_descendedOrbitSum` identifies the base
   change of the actual descended cocharacter with that orbit sum.
   `range_eq_parabolic_iff_baseChange` reflects the resulting all-test
   equality to `k`, using the monicity of `i` and the affine dynamic
   representative.

For the existence equivalence, the forward direction is ordinary base change;
the reverse direction applies the constructed descended presentation.

## Provenance and retained obligations

This is a derived result from the published modules
`Absolute.FixedTorusDynamicGalois`, `Absolute.CocharacterDescentLattice`,
`Absolute.SplitTorusDynamicDescent`, `Absolute.CocharacterAveraging`,
`Rational.RootSignParabolicLie`, `Dynamic.ConnectedProof` and
`GeometricConnectedness`. The conditional root criterion is used with its
remaining structural premise proved, so this construction has no unproved
statement as a hypothesis. No new assertion from external literature is
introduced.

The input includes the affine commutative group `T`, its map `j`, the finite
Galois splitting extension and an initial presentation of `i_K`. The
construction does not establish their existence from parabolicity, nor does
it prove that an arbitrary dynamic subgroup is geometrically parabolic. Those
remain obligations of the full `ParabolicDynamicStatement`.
