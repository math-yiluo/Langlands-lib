# Geometric unibranchness for local domains

This module specializes the geometric-unibranch definition to local domains
and integral schemes. Its source is the Stacks Project, Definition 15.108.1
([tag 0BPZ](https://stacks.math.columbia.edu/tag/0BPZ)) and Definition 28.16.1
([tag 0BQ2](https://stacks.math.columbia.edu/tag/0BQ2)). The registered local
snapshot is `stacks-valuation-normal-unibranch-2026-10-30`, files `0BPZ.html`
and `0BQ2.html`.

For a local domain `R`, `GeometricallyUnibranchDomain R` requires that
`integralClosure R (FractionRing R)` is local, that its canonical algebra
map from `R` is local, and that the residue-field map induced by this
algebra map is purely inseparable. Thus the predicate uses the actual
integral closure in Mathlib's fraction ring and the actual induced
residue-field extension. The source definition first takes the reduction;
the domain assumption already makes the ring reduced. This module does
not define geometric unibranchness for arbitrary rings with nilpotents.

`geometricallyUnibranchDomain_of_isIntegrallyClosed` proves this condition
for any local integrally closed domain. Integral closedness makes the
canonical map into the integral closure surjective: every integral
fraction comes from the original ring. A surjective map from a local ring
has local target and is a local homomorphism. The induced residue map is
surjective by lifting successively through the residue quotient and the
canonical map. Every residue element therefore comes from the source,
which implies both integrality and the required purely-inseparable
condition. This is the local-domain argument underlying Stacks Lemma
28.16.2 ([tag 0BQ3](https://stacks.math.columbia.edu/tag/0BQ3)); the proof
implements it through surjectivity rather than an explicit isomorphism.

`GeometricallyUnibranchIntegralScheme S` applies the local-domain predicate
to every actual structure-sheaf stalk of an integral scheme. Mathlib
supplies the domain and local-ring instances of these stalks.
`geometricallyUnibranchIntegralScheme_of_stalks` proves it when all stalks
are integrally closed, by the preceding local-ring theorem.

The universe is arbitrary, with no noetherianity, dimension or valuation-rank
assumption. This is a base-property prerequisite; it supplies no
correspondence representability, section extension or line-bundle extension.
