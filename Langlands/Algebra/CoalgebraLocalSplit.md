# Group-like bases from split reduced convolution duals over local rings

Let \(R\) be a commutative local ring and \(C\) an \(R\)-coalgebra. The
convolution dual means the actual algebra
\(D=\operatorname{Hom}_R(C,R)\), represented by `WithConv`. Cocommutativity
is not assumed. This module is an internally derived step in the special-fibre
multiplicative-type lifting argument.

## Extracting a basis

Assume first that the underlying module of \(C\) is finite free.
`exists_orthogonalIdempotent_basis` takes any family of orthogonal
idempotents \(e_i\) spanning \(D\) and gives a finitely indexed module basis
of \(D\) consisting of orthogonal idempotents. The input family need not be
finite or separately satisfy the sum-one condition.

The proof unwraps `WithConv` through its linear equivalence. The ordinary dual
of a finite free module is finite free, hence finitely presented and flat.
Mathlib's `Module.exists_basis_of_span_of_flat` over a local ring selects a
basis from the unwrapped generating family. The selected index map is
injective, because equality of selected generators would imply equality of
basis vectors. After transporting the basis back to \(D\),
`OrthogonalIdempotents.embedding` restricts the original orthogonality to the
selected indices. Finite generation makes the selected index type finite.
Its universe is the universe of the original family's index type, as in Lean.

`exists_groupLike_basis` applies the primal-basis construction of
`CoalgebraIdempotentBasis` to this orthogonal idempotent basis. It obtains a
finite module basis \(c_j\) of the original \(C\) satisfying both actual
group-like equations
\[
 \epsilon(c_j)=1,\qquad \Delta(c_j)=c_j\otimes c_j.
\]

## Through a nilpotent scalar quotient

Let \(I\subset R\) be nilpotent. Suppose a finite complete orthogonal
idempotent family spans
\(\operatorname{Hom}_R(C,R/I)\) as an **\(R\)-module**. This is the
quotient-valued convolution dual on the original coalgebra, exactly the target
of `CoalgebraNilpotentReduction.reduction`; an independently chosen model of
the base-changed coalgebra is not an input here.

`exists_groupLike_basis_of_nilpotent_reduction` lifts this family to spanning
complete orthogonal idempotents in \(D\), using
`exists_lift_spanning_completeOrthogonalIdempotents`, and then applies the
basis extraction above. Its result is a finite basis of group-like elements
of \(C\), with finite freeness of \(C\) as its module hypothesis.
`span_groupLike_eq_top_of_nilpotent_reduction` deduces that the full set of
group-like elements spans \(C\), by including the resulting basis in that
set.

The construction `groupLikeBasisOfNilpotentReduction` only assumes that
\(C\) is finite flat over the local ring. Finite flat modules over a local
ring are free, so the previous existence theorem applies. Choice packages
its finite index type, a `Fintype` instance and the basis with its group-like
proofs in a dependent pair. The input orthogonal family is finite and indexed
in the universe of \(C\), as specified by the declaration.

## Provenance and scope

These results are derived from local finite-flat basis extraction,
finite duality, and the two preceding internal coalgebra modules. No additional
literature assertion is made. Constructing the required quotient-valued
idempotent family from an actual split reduced coalgebra, constructing group
scheme isomorphisms, and lifting a splitting cover are subsequent
obligations. The fibrewise central-isogeny criterion remains open.
