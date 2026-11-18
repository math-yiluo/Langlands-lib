# Association of actual semistandard spectral indices

Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, Remark VII.2.4, printed p. 320 (PDF p. 86), associates
two indices `(O,P=MU)` and `(O',P'=M'U')` when some element of `W^G` takes
`M` to `M'` and `O` to `O'`. The parabolic fibers `P(M)` are those in I.1,
printed p. 238 (PDF p. 4). Source ID `waldspurger-2003-plancherel`.

`orbitConstituents` realizes `O` as the set of its actual discrete-series
constituents in the smooth dual of the literal Levi. A representative of
the quotient shows that equal constituent sets over a fixed parabolic
give equal orbit classes. `ConjugatesLevi` is the equality of all-test
Levi functors under inner conjugation. Its pointwise restriction
`leviPointConjugation` is the continuous multiplicative equivalence
`m ↦ n m n⁻¹` on the actual Levi groups. `OrbitConjugates` requires this
all-test equality and equality of the full constituent sets under
pullback by the inverse point conjugation. `WeylTransports` uses lifts
of an element of the actual relative Weyl quotient `N(F)/Z(F)`.

An inner conjugation by a point of the source Levi preserves every
constituent, by the smooth representation equivalence for inverse
conjugation. Thus when `torusCentralizer i ≤ t.1.levi`, any two lifts of
the same Weyl element induce the same transport relation. This is
`weylTransports_mk_iff`. The all-test equality underlying the relation
then agrees with the published `relativeWeylConjugateSubgroupFunctor`.
Identity, inverse and composition of the actual conjugations and
pullbacks prove that `Associated`, the existence of a Weyl transport,
is an equivalence relation. `AssociationClass` is its quotient, and
`associatedIndices` gives its individual classes as sets of full indices.

For a fixed Weyl element, every transported index has the same target
Levi. Two transported indices with the same target parabolic have the
same constituent set and hence the same orbit. If there is a transported
index, projection to the parabolic therefore injects the transport
fiber into the actual parabolic fiber over that index's Levi. This
proves `finite_associatedIndices` from
`IsConnectedReductive.finite_relativeWeylGroup`, the source Levi's
centralizer containment, and `SemistandardSpectralFiberFinitenessStatement`.
The finite union of these classes over a finite set proves
`finite_associationSaturation`, with containment supplied by
`SemistandardLeviCentralizerContainmentStatement`. The latter is available
conditionally via `semistandardLeviCentralizerContainment_of_dynamicCoverage`
from the exact `SemistandardSpectralDynamicCoverageStatement`. The
finiteness propositions here concern the geometry and saturation of a
given finite input index set.

The construction uses the intrinsic semistandard family of Task 7229 and
the all-test Weyl transport interface of Task 7263. It supplies the
association relation and finite support bound for VI.3 and VII.2.4. The
normalized coefficient comparison, its induced action on sections and
transport of the packet and form integrals are separate inputs to the
averaging and representative-sum formulas.
