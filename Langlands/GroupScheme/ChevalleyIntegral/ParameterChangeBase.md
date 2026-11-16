# Restriction of ordered cell parameters along a change of base

This internal construction compares the explicit parameter schemes of
`IntegralProductEmbedding` and `AmbientProductCell` along an arbitrary morphism
`Spec S → Spec R`. It uses supplied integral Chevalley data and does not require
that either base ring be a field.

An ordered root parameter point is the family of its polynomial coordinates
in the global sections of the test scheme. The relative spectrum adjunction
and polynomial evaluation give an equivalence with these families. Under this
equivalence, the ordered root map is the stated matrix product on every test
scheme, with coefficients zero outside the root list.

`matrixRestrict` uses the canonical base-change isomorphism for the general
linear group and the pullback adjunction. It preserves the matrix point, is
natural in the test scheme, and preserves multiplication. The same polynomial
coordinates define `orderedRootRestrict` over the old base, compatibly with the
matrix product. The full character-valued point similarly gives `torusRestrict`
using the canonical base-change isomorphism for diagonalizable groups. It keeps
the entire character lattice.

The product `orderedCellRestrict` restricts the negative ordered root parameters,
the full-lattice torus point, and the positive ordered root parameters, with the
same association as `orderedCellSpace`. Its composite with the ordered matrix
cell map is exactly the restriction of the original matrix triple product.
These are actual scheme morphisms over `Spec R`; the construction does not yet
identify an integral closure with this cell or prove integral reductivity.
