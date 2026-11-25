# Admissible epimorphisms under actual affinoid pushout

This module proves that the actual second leg of an affinoid pushout is an
admissible epimorphism whenever the original first map is an admissible
epimorphism. The other original map is an arbitrary bounded algebra map between
presented affinoids over the same complete ultrametric normed field. The proof
retains arbitrary positive radii, trivial valuations, nonreduced and zero
algebras, and empty spectra.

This is internal derived infrastructure from `ClosedQuotientBaseChange`,
`ClosedQuotient` and the actual bounded affinoid pushout universal property.
The closed-ideal extension helper of `FiniteDomainIdealDescent` is an indirect
dependency. No new
original-source assertion is used.

`mapOfLeftEquiv` transports the first pushout algebra through a supplied
bounded equivalence over the base, leaving the second algebra and its original
map unchanged. It is the actual bounded pushout lift of the transported first
leg and the unchanged second leg. The two leg equations are entire bounded-map
equalities. The inverse bounded equivalence gives `inverseOfLeftEquiv`.
Pushout uniqueness and the bounded equivalence's inverse identities show that
the forward transport has this constructed bounded section. Consequently the
forward transport is admissible. Its composite with the original second leg is
exactly the changed second leg, proving
`rightMap_isAdmissibleEpi_of_leftEquiv`.

For `rightMap_isAdmissibleEpi`, the kernel of the original admissible epimorphism
is closed by continuity. `ClosedQuotient.equivOfAdmissibleEpi` identifies its
target with the actual presented quotient by that kernel, with the inverse bound
supplied by the original norm-controlled lifts. Base change of that presented
quotient has an admissible second leg by `ClosedQuotientBaseChange`. Transporting
the first algebra through the constructed bounded equivalence proves the
conclusion for the unchanged original map.

Admissibility includes surjectivity and positive two-sided comparison of the
actual quotient seminorm with the stored target norm. The proof supplies those
bounds through controlled lifts and bounded sections, without using an open
mapping theorem or a nontrivial coefficient valuation. This module does not
assert finite ideal descent or the full special-set intersection theorem.
