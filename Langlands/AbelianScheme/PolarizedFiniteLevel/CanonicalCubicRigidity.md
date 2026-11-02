# Cubic section rigidity using canonical bundle transport

For an ordinary polarized finite-level datum over a field, and an actual
polarized automorphism `α`, `canonicalCubicSectionCoordinateEquiv` constructs
an actual coordinate linear equivalence from a specified finite ordered basis
of all sections of the datum's actual cubic bundle. It supplies the actual
`α.cubicBundlePullbackIso` constructed from the polarization equation to the
existing section-coordinate construction. There is no separate bundle
preservation or coordinate-lift input.

If these basis sections generate at every scheme point,
`cubicSectionMap_canonical_equivariant` proves equality of actual scheme
morphisms: the underlying automorphism followed by the cubic section map
equals that section map followed by the induced projective linear action.
The action uses the dual of section transport in the coordinates of the
dual basis, with the conventions of `SectionAction`.

Over an algebraically closed field,
`eq_refl_of_canonicalCubicSectionBasis` concludes equality of the actual
polarized automorphism with the identity. Its inputs are positive level,
the generating full section basis, monomorphy of its actual section map,
a uniform bound `q` for actual torsion sections lying in each nonzero linear
hyperplane, and the strict inequality `(m+1)*q < n^(2*g)`. Canonical bundle
transport supplies the isomorphism required by the existing section-basis
rigidity theorem.

`eq_refl_of_canonicalCubicSectionBasis_count` applies the exact supplied
`CubicTorsionHyperplaneBoundStatement`. It retains positive dimension,
polarization index and level, nonzero level in the field, the generating full
section basis, an actual closed immersion of its section map, and the strict
inequality
`(m+1)*(6^g*d*g!*n^(2*g-2)) < n^(2*g)`.
The existing cubic nondegeneracy theorem and projective-twist comparison
supply the count's corresponding geometric premises. The canonical bundle
comparison supplies the automorphism's bundle transport.

`Datum.polarizedIsoSubsingleton_of_cubicSectionBasis_count` uses the same
hypotheses on the source datum to show that the type of actual polarized
isomorphisms from it to any other datum of the same indices is a subsingleton.
Compose one isomorphism with the inverse of the other, apply the preceding
automorphism theorem, cancel the inverse, and use proof irrelevance for
the polarization and level equations. No such isomorphism is asserted to
exist.

These are internal compositions of `PolarizedBundleTransport`,
`CubicSectionRigidity` and `CubicSectionNondegeneracy`, with no new external
source assertion. They prove no section-basis existence, generation,
closed-immersion theorem, geometric torsion count, eventual numerical range,
or ordinary moduli representability. Coherence of the chosen bundle and
coordinate comparisons under automorphism composition is not asserted.
