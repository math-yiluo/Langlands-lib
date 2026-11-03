# A canonical representative of a trivial unipotent radical

This derived construction provides an actual representative when the existing
ground-field predicate `HasTrivialUnipotentRadical G` is supplied. It does not
derive that predicate from geometric reductivity and does not assert radical
existence for arbitrary groups.

For a separated group scheme over a field, `trivialUnipotentRadical` returns
the trivial group scheme over the field, its unit homomorphism `kernelUnit G`,
and a proof that this homomorphism satisfies `IsUnipotentRadical`. The existing
category-theoretic trivial group has the base scheme as its underlying
scheme.

The proof first identifies the image of the unit homomorphism with the
identity subgroup on every relative test scheme. Separatedness makes the
identity section a closed immersion. The trivial group is smooth and
connected over a field. Each of its representations takes every point to the
identity matrix, so the constant vector with every coordinate equal to one
is a nonzero fixed vector in each nonempty finite coordinate space. Its
all-test subgroup is normal because it consists of identity elements.

Finally, `HasTrivialUnipotentRadical G` says that every eligible smooth,
connected, unipotent normal closed subgroup has trivial all-test image.
This gives the greatest-subgroup property required by `IsUnipotentRadical`.
The construction uses only the published predicates and their elementary
consequences; it is internal infrastructure for a reductive
parabolic/pseudo-parabolic comparison.

The unit range and separated closedness facts are shared through [UnitSubgroup](../UnitSubgroup.md); closedness uses the existing `kernelUnit_isClosedSubgroup` declaration.
