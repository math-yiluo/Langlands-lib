# Matrix groups over number-field adeles

This file specializes Mathlib's matrix unit groups to the actual full, finite,
and infinite adele rings of a number field. The field has arbitrary universe
`u`; the matrix indices are `Fin n`. The constructions make sense also at
rank zero. Applications to automorphic representations will require positive
rank explicitly.

`RationalGL`, `AdelicGL`, `FiniteAdelicGL`, and `InfiniteAdelicGL` use Mathlib's
`Matrix.GeneralLinearGroup` directly. The topologies on the adelic groups are
the unit-group topologies of their matrix rings, including the inverse
coordinate. The finite coefficient ring uses its restricted-product topology.
No topology on the rational field is selected.

`AdelicGL.rational` is the entrywise algebra map, and its injectivity is proved
from injectivity of the number-field diagonal map. The continuous projections
`infinite` and `finite` are entrywise coefficient projections. `pair` constructs
an inverse in the full ring by pairing the two given inverse matrices.
`split` is the resulting multiplicative homeomorphism with the product.
`ofInfinite` and `ofFinite` are its two group inclusions, with identity in the
other factor. `determinant` takes values in actual ideles; `scalar` is the
continuous scalar-matrix map, whose image commutes with all adelic matrices.

The source is A. Borel and H. Jacquet, “Automorphic forms and automorphic
representations,” *Automorphic Forms, Representations and L-Functions*,
Proc. Sympos. Pure Math. 33, part 1 (1979), pp. 189–202, specifically §3.1–3.2
and §4.1, printed p. 194 (one-based PDF page 189 of the retained `Part I.pdf`).
The explicit matrix-coordinate construction of the product decomposition is
derived implementation content for `GL_n`, proving the group and continuity
fields of the source's decomposition.

This is the matrix-group prerequisite for actual automorphic function spaces.
It does not construct their analytic conditions, assert discreteness of
rational points, identify local restricted products of matrix groups, or
reimplement the neighboring branch's general parabolic geometry.
