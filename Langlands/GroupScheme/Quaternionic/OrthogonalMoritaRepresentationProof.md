# Orthogonal Morita comparison with the actual coefficient row action

Authors: Worker 334 and Worker 257.

`orthogonalMoritaRepresentation` proves the unchanged Library proposition
`Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentationStatement.{u}`
for every universe `u`. Its hypotheses are precisely those of that proposition:
an arbitrary field `K`, a finite-dimensional central division `K`-algebra `D`
of dimension `degree²` with `degree > 0`, integers `m,n` satisfying
`n ≥ 4` and `m * degree = 2 * n`, a first-kind involution whose symmetric
subspace has dimension `degree * (degree + 1) / 2`, a nondegenerate quadratic
class `q`, and an algebraically closed extension `L/K`.

The resulting `OrthogonalMoritaComparison` contains an actual group-scheme
isomorphism after base change to `L`, a fixed `L`-linear row equivalence,
and the required action equality over every compatible commutative
coefficient `L`-algebra. This is an internal assembly of the published algebra
splitting and hyperbolic-basis theorems with the explicit Morita constructions
in `OrthogonalMoritaRows`, `OrthogonalMoritaRowBasis`,
`OrthogonalMoritaSplitUnits`, and `OrthogonalMoritaAffine`.

For a supplied splitting `e` and mutually inverse hyperbolic basis matrices
`P,P'`, `splittingUnitComparison` packages `splitUnitsEquiv` and its
coefficient naturality. At every coefficient algebra `R` its matrix formula is
`P_R * matrixChartR(e,R,y) * P'_R`, with `y` the underlying original
isometry unit. The input hyperbolic condition is equality of quadratic
matrices modulo alternating matrices. The split-unit construction transports
the original quadratic defect, so this comparison retains the quadratic
equations in characteristic two as well.

`comparisonOfSplitting` uses `UnitComparison.groupIso` to reconstruct the
actual group-scheme isomorphism from this natural family. Its row equivalence
is `basisRowEquiv`: split `L ⊗_K D^m` into `degree` rows of length
`m * degree`, then multiply each row on the right by `P'`.
The coefficient extension is the canonical `rowEquivOver` of that fixed
`L`-linear equivalence.

To verify the action equality, read an original affine point as the unit
`y` using `isometryAffineUnitsEquiv`. The formula
`affineMatrix_splitPoint` identifies the reconstructed split matrix with
`toGL` of the supplied unit comparison. Preservation of inverse, together
with the equality between the inverse of a general linear unit and the
nonsingular inverse of its matrix, identifies the inverse split matrix with
the conjugated matrix of `y⁻¹`. The underlying inverse unit is exactly the
inverse of `isometryAffineUnitsOver` read through the original closed
inclusion. Applying `basisRowEquiv_rightAction` to this tensor-matrix
element proves the required intertwining of the original inverse-right
tensor-row action. The argument quantifies over all tensor rows and all
compatible coefficient algebras, including any specified compatible
`K`-action.

Finally, `CentralSimple.exists_matrix_chart` supplies a splitting over the
given `L`. `finrank_eq_matrix_size` and injectivity of squaring on natural
numbers identify its matrix size with `degree`.
`isUnit_splitGram_polar` transports the nondegenerate polar unit of the
chosen representative `Quotient.out q` to the split Gram matrix.
The equation `m * degree = 2 * n` gives the required cardinality for
`OrthogonalMatrix.exists_hyperbolic_matrix`, which supplies `P,P'` and the
hyperbolic congruence. Substitution into `comparisonOfSplitting` completes
the proof.

All constructions preserve the proposition's field and characteristic
scope, including finite base fields and characteristic two. The proof uses
no spin-cover weight, type-D classification, or Kneser–Tits assertion.
