# Fixed exponent norms throughout actual unitary twist families

This derived module is supporting infrastructure for the uniform exponent
polynomials in Waldspurger VI.2.1 and VI.2.3. It uses the published actual
normalized Jacquet module and full geometric-lemma pieces; it does not select a
generic locus of the parameter torus. The local-field and representation carrier
universes remain independent.

`normalizedJacquetExponentNormSet` records the nonnegative real norms of the
actual normalized Jacquet exponents at one specified point of its actual split
component. The published arbitrary-parabolic exponent theorem makes this set
finite for an admissible finite-length ambient representation.

The unramified Jacquet twist formula expresses a twisted exponent as an untwisted
exponent times the original ambient twist restricted through the actual scheme
maps. For a unitary twist, the second factor has norm one. This proves inclusion
of the twisted norm set in the untwisted one without any admissibility or finite
length premise for the inclusion itself.

For an actual `GeometricLemmaIntersectionDatum`, the target split component is
factored through a split component of the inner intersection Levi using the
specified morphism and compatibility equality. The full-piece exponent transport
then gives an untwisted inner source Jacquet exponent times a restriction of the
source twist. Admissibility of the twisted inner Jacquet module is derived from
the published arbitrary-parabolic Jacquet admissibility theorem and the exact
point-group transport. The norm of that exponent at the pushed-forward point
therefore belongs to the fixed finite norm set of the untwisted inner source
Jacquet module. This holds for every unitary unramified source twist and every
full-piece exponent. No distinctness of specialized characters is required.

The context is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra* (2003), source `waldspurger-2003-plancherel`,
proof of VI.2.1 on printed pp.297–298 and proof of VI.2.3 on printed p.300.
The implemented proof composes published actual Jacquet exponent and twist laws.
The module does not prove nilpotence orders uniform in the parameter, contraction
of nonunitary exponents, or the full positive-decay estimate. Transport from the
finite collection of full pieces to the actual induced Jacquet module is still
required by that application.
