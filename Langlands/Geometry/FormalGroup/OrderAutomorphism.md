# Actual integral full-order formal automorphisms

`OrderAction.Automorphism E` is the type of actual integral full-order formal
isomorphisms from a supplied module to itself. Its group multiplication is
ordinary functional composition: the right factor is applied first. The
inverse is the stored actual inverse formal map, and the identity is the
actual identity formal map. The group laws follow from formal composition
and the two stored inverse equations.

`Automorphism.mapHom` extends both actual inverse maps along a coefficient
algebra map and is a homomorphism of these groups. Integral coefficient
extension preserves identity, composition and inversion. The actual
coefficient-composition isomorphism is natural in every integral full-order
isomorphism: its complete coordinate equation follows from coefficient
mapping of the full original formal series and composition of the ring maps.
The proof uses formal-map extensionality, rather than detection on points.

The scalar ring, acting ring and coefficient rings retain separate scalar,
acting and coefficient universes. The coefficient rings of the composition
comparison share the same universe, as in the existing actual `mapCompIso`.
Coordinate types are arbitrary and finite. No domain, rational-field,
height or representability assumption is needed.

This is internal group structure on actual maps. It supplies a prerequisite
for frame precomposition; it does not identify these automorphisms with a
matrix group or assert the full Drinfeld product-group action, Frobenius
comparison, determinant-height formula, or a representing object.
