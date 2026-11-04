# Finite coefficient spaces for actual conjugation

This internal supporting construction proves local semisimplicity of the actual
coordinate conjugation derivation over an algebraically closed field. It derives
from the imported finite coefficient theorem for coalgebras, actual matrix
representations and their tangent identities, and semisimplicity under surjective
intertwiners. It assumes no additional structural theorem from the literature.
The general-field descent and the Cartan-generation theorem remain separate
obligations.

Throughout, `k` is a field in an arbitrary universe and `G` is an actual affine
group scheme over `Spec k`. No smoothness, connectedness or finite type assumption
is imposed in this module. Finite matrix indices may be any finite type in
`Type`, including the empty type. Algebraic closedness is used only in the final
two semisimplicity results.

`representationCoefficients G ρ` is the matrix of an actual representation `ρ`
at the universal point of the chosen coordinate algebra `B` of `G`.
`affineMatrix_eq_coefficients` proves that its evaluation by the coordinate
homomorphism of any actual affine point is the matrix of that point. The proof
uses naturality and the universal-point identity, so it applies to every
commutative test algebra, including algebras with nilpotents.

`conjugationDerivation_coefficients` computes the action of the actual global
conjugation derivation `D` associated with `X : lieKernel G k` on this matrix:
`D(M) = TM - MT`, with the entries of the tangent matrix `T` extended from `k`
to `B`. The private matrix helpers extract constant and epsilon coefficients of
products of dual-number matrices. Actual infinitesimal conjugation at the
universal point then has matrix `(I + εT) M (I - εT)`, which yields the formula.

`exists_representation_coefficient_span` shows that every element of `B` lies in
the linear span of the universal coefficients of some actual finite
representation of `G`. The proof applies the imported finite coefficient theorem
to the singleton in the coordinate coalgebra. Its matrix satisfying the
comultiplication and counit identities defines an actual representation of the
corepresented group model. Restriction through the inverse model isomorphism
makes it a representation of the original `G`. The underlying inverse scheme
map and the universal-point calculation identify its coefficients with the
original coalgebra matrix. In particular, no finite type hypothesis or rational
point density assertion is needed.

`coefficientLinearMap G ρ` sends formal coordinates indexed by pairs `(i,j)` to
`sum v(i,j) • M(i,j)` in `B`. `coefficientLinearMap_intertwines` proves that this
map intertwines `D` with the **negative** tangent endomorphism of the actual
representation `ρ.dual.tensor ρ`. The sign follows from the convention
`D(M) = TM - MT`. The proof checks the identity on the standard coordinate basis,
using the dual and tensor tangent identities, and sums the Kronecker deltas.
`coefficientLinearMap_range_invariant` consequently proves that its range is
invariant under `D`.

Over an algebraically closed field,
`IsSemisimpleElement.isSemisimple_coefficient_range` proves semisimplicity of
`D` restricted to this range. Representation-tested semisimplicity of `X`
applies to the actual dual-tensor representation; semisimplicity survives
negation, and the coefficient map onto its range is a surjective intertwiner.
Finally `IsSemisimpleElement.locallySemisimple_conjugationDerivation` places each
coordinate in one such range. Each range is finite dimensional because the
formal coefficient space is finite dimensional. This supplies exactly the
imported `LocallySemisimple` predicate: every coordinate belongs to a finite
dimensional invariant subspace on which the restriction is semisimple. The
result preserves arbitrary characteristic and does not assert local
semisimplicity over an arbitrary nonclosed field.
