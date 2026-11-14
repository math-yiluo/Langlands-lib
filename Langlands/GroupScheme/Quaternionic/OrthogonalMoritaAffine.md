# Affine reconstruction of a natural orthogonal unit comparison

Authors: Worker 257 and Worker 334.

This internal categorical construction takes a natural family of isomorphisms
between the original tensor-algebra isometry units and split orthogonal
matrices. It makes no existence assertion about that family. Its input
`UnitComparison` retains every compatible coefficient algebra and every
coefficient map.

The scope is an arbitrary universe `u`, a field `K`, a finite-dimensional
division `K`-algebra `D`, a first-kind involution `σ`, a quadratic form `q`
on `Fin m`, a field extension `L/K`, and a natural number `n`. No
characteristic or infinitude hypothesis is added. The supplied comparisons
are multiplicative equivalences with the split orthogonal group on
`Fin n ⊕ Fin n`, for every commutative `L`-algebra equipped with a
compatible `K`-algebra structure.

`isometryAffineUnitsEquiv` reads actual affine points through the published
corepresentation of the isometry cut. Its value is exactly the unit read
through the original closed inclusion, now refined by its defining equations.
The refinement is natural by the published naturality of those units.

`UnitComparison.pointEquiv` composes the actual base-change point equivalence,
this refinement, the supplied isomorphism, and the inverse of the explicit
orthogonal affine point corepresentation. Naturality of the first step follows
from its formula as the first projection of the pullback. The other steps
are natural by their corepresentations and the supplied hypothesis.
`AffinePointComparison.iso` then reconstructs the actual group-scheme
isomorphism, and its point formula shows that reconstruction retains the
specified coefficient comparison.

`affineMatrix_splitPoint` identifies the matrix of the resulting split
point through the published orthogonal inclusion with `toGL` of the
supplied unit comparison. It applies to every compatible coefficient
algebra, including a specified `K`-action rather than only the canonical
composite action. The proof first establishes the formula for the
composite action using the affine-point reconstruction and inclusion
formulas. The scalar-tower identity makes every compatible `K`-action
equal to that composite action, so equality elimination gives the full
formula.

This is a supporting construction, not a proof of
`OrthogonalMoritaRepresentationStatement`: constructing `UnitComparison`,
choosing the fixed row equivalence, and proving the final row-action
intertwining remain separate obligations. Its provenance is internal:
it composes published corepresentations and actual pullback point
equivalences and applies the published affine reconstruction theorem.
