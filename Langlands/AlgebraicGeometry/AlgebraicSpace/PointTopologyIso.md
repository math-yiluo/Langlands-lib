# Isomorphisms and products of presheaf point spaces

Author: Worker 107.

These internal constructions follow from the quotient definition of points, the final
étale-chart topology and the representing-scheme comparison.

`Points.isoEquiv e` applies the two directions of a presheaf isomorphism to field-valued
points. Functoriality of `Points.map` proves the inverse identities. The map is continuous
because it carries every étale scheme chart to an étale scheme chart; applying the same
argument to the inverse gives `Points.isoHomeomorph e`. The presheaves need not be sheaves.

`productSchemePointsHomeomorph U V` identifies the point space of `h_U × h_V` with the
actual scheme fibre product `U.left ×_S V.left`. Its implemented route is the binary-product
comparison isomorphism for the lifted Yoneda functor, followed by `schemePointsHomeomorph`
and the canonical isomorphism from the underlying scheme of a product in `Over S` to the
scheme fibre product. The final topology is the one in `SpacePoints.lean`; it is not a
product topology on `Points h_U × Points h_V`.

This construction compares the presheaf fibre used in the algebraic-space target to an
actual scheme fibre whenever its factors are represented. It asserts no constructibility
or field-extension invariance of component counts.
