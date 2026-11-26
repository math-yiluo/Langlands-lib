# Change of geometric point and base for principal Harris markings

The comparison in `HarrisIntegralPrincipalFullLevel` uses a geometric
reference point for the invariant adelic orbit and for the lifting condition
on an ordered full-level marking. The declarations here identify how the
comparison behaves under a change of that point and under pullback of the
actual polarized action.

## Geometric points

`harrisPrincipalFullLevelEquiv_point` compares the markings of an invariant
normalized principal orbit at two algebraically closed points of the same
connected, locally noetherian, quasi-separated base. The level subgroup
equals the principal congruence subgroup at the positive modulus `m`.
The comparison takes the full adelic tower inputs at both points, including
invertibility of every positive integer on the base, finite cover fibres,
and the finite-étale torsion and roots-of-unity inputs.
Transporting the orbit by the existing
geometric path equivalence preserves every ordered global section by
`harrisIntegralOrderedFullLevel_normalizedTransport`. The sections determine
the full-level structure.

The bijection between orbits and compatible markings then proves
`harrisPrincipalFullLevelCondition_iff_point`. The proof moves an orbit
giving the marking in either direction along a geometric path.
`harrisPrincipalFullLevelGeometricEquiv` is the identity on the underlying
markings with the geometric lifting condition transported by this
equivalence. Its definition therefore gives a comparison independent of
the path. This uses the geometric-point comparison for invariant adelic
level structures described in Harris–Taylor III.1.

## Base change

`harrisPrincipalFullLevelCondition_iff_baseChange` compares a marking over
`S` evaluated at the composite `t ≫ b` with its ordinary pullback along
`b : T ⟶ S` evaluated at `t` over quasi-separated bases. It uses the existing actual pulled-back
polarized action with its dual data and the required frame nonemptiness
for that construction. Finite torsion base change identifies the two
coordinate maps on each standard basis vector by `fibreTuple_pullback`
and hence on the full residue module. The published frame equivalence
preserves and reflects normalization and commutes with finite reduction.
It carries the geometric lift in both directions.

`harrisPrincipalFullLevelEquiv_baseChange` uses
`harrisIntegralLevelSections_baseChange` to compare the ordered sections
of the pulled-back invariant orbit with the pulled-back sections of its
marking over connected, locally noetherian bases with the full adelic
tower inputs on both bases. The two resulting restriction maps agree by the
identity composite in the over category. The equality concerns the same
actual abelian scheme and the original pullback of the normalized
adelic orbit.

Source for the invariant-level point comparison
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`,
III.1, printed p. 91 (PDF p. 99). The ordinary markings and their base-change
comparison are internal consequences of the principal-level construction.
