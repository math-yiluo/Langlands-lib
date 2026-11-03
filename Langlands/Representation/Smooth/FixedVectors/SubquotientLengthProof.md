# Proof of compact-open subquotient detection and length reduction

Worker 1210. Worker 189 contributed the agreed interface and its role in the
Howe implication.

`Langlands.compactOpenSubquotientLengthReduction` proves exactly
`Langlands.CompactOpenSubquotientLengthReductionStatement`, preserving the
independent group and representation-carrier universes. This is an internal
proof using published compact-open exactness and the elementary fixed-vector
length criterion.

`compactOpenSubquotientFixedVector` forms the actual inclusion intertwiner
from `T` into the given smooth representation. Injective smoothness transfer
proves that `T` is smooth. It then forms the actual quotient intertwiner from
`T` onto `LengthCriterionProof.quotientRep S T`. Surjective smoothness transfer
proves that this quotient is smooth. The quotient map is the standard
`Submodule.mkQ`, and its kernel is the actual lower submodule pulled back to
`T`.

Nontriviality of the quotient's fixed-vector space supplies a nonzero fixed
vector `w`. `Langlands.Compact.fixedVectorSurjectivity` lifts `w` to a vector
`v` fixed by `K` in `T`. The ambient image of `v` is fixed because the inclusion
is equivariant. If it belonged to `S`, `Submodule.Quotient.mk_eq_zero` would
make its quotient image zero. This contradicts the choice of `w`. The result
is precisely the direct ambient witness required for each strict inclusion.

`compactOpenSubquotientLength` applies this construction to the assumed
nontrivial fixed space in every strict successive subquotient. It then invokes
`Langlands.fixedVectorsStrictInclusionLength`: intersections with the ambient
fixed space strictly increase along strict subrepresentation chains, so their
finite dimensions bound the chain length. The resulting conclusions use actual
composition series and actual finite length over the group algebra.

The proof does not construct a compact open subgroup detecting all strict
subquotients of a reductive rational-point representation. That structural
step, the unrestricted Howe implication, its converse, the VI.6.3 intermediate
assertions, and the source's stronger specially chosen subgroup bound remain
separate obligations.
