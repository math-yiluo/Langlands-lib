# The convolution dual of a scalar-extended coalgebra

Let \(R\to S\) be a homomorphism of commutative rings and \(C\) an
\(R\)-coalgebra. This internally derived unit compares the actual convolution
dual of \(S\otimes_R C\) with \(S\)-valued convolution functionals on the
original coalgebra. It then supplies the input for nilpotent lifting of a
finite group-like basis over a local ring. Cocommutativity is not assumed.

## Coordinates of a group-like basis

For any finite basis \(b_i\) of \(C\), `coordinateBasis` regards its dual
basis as a basis of the convolution algebra
\(\operatorname{Hom}_R(C,R)\), represented by `WithConv`. Its evaluation is
exactly the corresponding basis coordinate.

If every \(b_i\) is group-like, then
`coordinateBasis_completeOrthogonalIdempotents` proves that the coordinate
functionals form a complete orthogonal idempotent family. The convolution
product evaluated on a basis vector is the product of its two coordinates,
since \(\Delta(b_k)=b_k\otimes b_k\). Kronecker coordinates show that
\(e_i e_j=\delta_{ij}e_i\). Evaluation on the basis also proves
\(\sum_i e_i=1\), because the counit is one on every group-like basis vector.

## Restriction and scalar generation

`restriction` is the actual \(S\)-algebra equivalence
\[
 \operatorname{Hom}_S(S\otimes_R C,S)_{\mathrm{conv}}
 \simeq \operatorname{Hom}_R(C,S)_{\mathrm{conv}},
 \qquad f\longmapsto(x\mapsto f(1\otimes x)).
\]
The inverse extends an \(R\)-linear functional by tensor linearity. Tensor
extensionality proves that the two constructions are inverse. The
comultiplication formula for a scalar-extended coalgebra proves compatibility
with convolution, and the counit gives scalar compatibility.

For a finite \(S\)-basis \(b\) of \(S\otimes_R C\),
`restrictedCoordinateBasis` transports its coordinate basis through this
equivalence. It is an \(S\)-basis of \(\operatorname{Hom}_R(C,S)\), with
\(i\)-th functional \(x\mapsto b_i^*(1\otimes x)\). If \(b\) is group-like,
`restrictedCoordinateBasis_completeOrthogonalIdempotents` maps its complete
orthogonal family through the ring homomorphism underlying `restriction`.

If \(R\to S\) is surjective, `restrictedCoordinateBasis_span` proves that
these functionals span as an **\(R\)-module**. The proof uses Mathlib's
`Submodule.restrictScalars_span`: surjectivity permits every \(S\)-scalar
in a linear combination to be replaced by an \(R\)-scalar. Applying this to
the spanning equality of the transported \(S\)-basis gives the assertion.

## Lifting from the actual reduced coalgebra

Suppose \(R\) is local, \(I\subset R\) is nilpotent, and \(C\) is finite
flat over \(R\). Given a finite group-like basis of the actual coalgebra
\((R/I)\otimes_R C\), `groupLikeBasisOfReducedBasis` constructs a finite
group-like basis of \(C\). The input index type and the resulting index type
lie in the universe of \(C\), as specified by Lean. The construction does
not assert that the chosen basis reduces to the supplied basis or preserves
its indexing.

The proof applies the preceding restriction results with \(S=R/I\).
Surjectivity of the quotient map supplies the required \(R\)-linear
spanning. `CoalgebraLocalSplit.groupLikeBasisOfNilpotentReduction` then
lifts the complete orthogonal family and recovers a group-like basis of the
original coalgebra. `span_groupLike_eq_top_of_reduced_basis` deduces that
all group-like elements span \(C\), by including this basis in their set.

## Provenance and scope

Worker 626 derived this unit from tensor extension of linear maps, convolution,
finite dual bases, and the preceding internal nilpotent-reduction and local
basis units. No additional literature assertion is made. The input is a
basis of the actual scalar-extended coalgebra, so the quotient-valued dual
family is now constructed rather than assumed. Passing from group-scheme
base change to these coordinates, reconstructing a diagonalizable group,
and lifting a splitting cover remain separate obligations. The fibrewise
central-isogeny criterion remains open.
