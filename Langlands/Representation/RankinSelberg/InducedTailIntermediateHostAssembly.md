# Assembly with exact intermediate-tail prerequisites

`InducedTailIntermediate.intermediateRankSpan_of_exact_prerequisites` proves
`InducedTailIntermediateRankSpanStatement` from the five exact prerequisite
statements retained in the published host-assembly interface, in order:
conditional diagonal-extension span, actual two-block Whittaker extension,
full normalized-product Whittaker type, actual lower-block quotient
disintegration, and actual inverse-character value-set equality. The field,
two block carriers, and test carrier have four independent universes. The
wrapper in `InducedTailIntermediateHostAssemblyProof` gives the theorem of the
existing `InducedTailIntermediateHostAssemblyStatement`.

## Full Whittaker type and dependent transports

The private lemma `twoBlock_type_of_statement` specializes full
normalized-product Whittaker type to the literal ordered two-block shape.
It identifies the shape and representation family by equality in a dependent
sigma type, so the tensor carrier and canonical normalized induction remain
the existing constructions. The main theorem applies this lemma to the actual
ULift-conjugated block representations. Their module equivalences transfer
Whittaker type from the original representations. Both lifted carriers lie in
`max uV₁ uV₂`; the actual induced carrier lies in `max uF uV₁ uV₂`, as required
by the conditional span premise.

`representationRankCast` transports a representation along equality of rank
indices while retaining its carrier. `type_rankCast` transfers full Whittaker
type along the same equality. `valuesAt_block_eq` transports the block index
and its dependent rank equation together. `valuesAt_rankCast` identifies the
rank-indexed value set with the value set of the transported representation.
All three transport lemmas reduce to equality substitution.

## Assembly on actual tail values

For the strict intermediate-rank inequalities, the proof writes the test index
as `t = b + (k + 1)` and sets `c₀ = a + 1 + b - t - 1`. The resulting rank
equalities identify the canonical induced representation with the rank used by
the conditional diagonal-span premise. The supplied scalar self-dual Haar
measure and the two independently supplied compatible quotient measures remain
the measures in the target value sets.

The proof uses `Submodule.span_le` to reduce the Laurent-span inclusion to each
generator `R` in the tail value set. The explicit inverse-character premise
rewrites that membership at the inverse character. The zero-row adapter
`exists_reversedTail_of_mem_scaled` then extracts actual inverse test and
standard tail coefficients, absolute integrability on a right half-plane, and
rational continuation with the same `R`. The main assembly uses this adapter
with the retained premise; it does not use the separate compatible-measure
adapter to discharge that premise.

The two-block extension premise, through the published pointwise adapter,
constructs a diagonal coefficient of the actual canonical induction for every
Schwartz--Bruhat test function. The rank cast preserves membership in its
Whittaker coefficient image. The compatible tail quotient measure is
sigma-finite. Published analytic properties give sigma-finiteness, positivity
on open sets, and finiteness on compact sets for the actual rectangular
product of the supplied scalar Haar measure. The actual disintegration
premise supplies the triangular measure, these same three properties, and a
strictly positive normalization. The proof passes that normalization and its
positivity unchanged to the conditional diagonal-span premise; its Laurent
span calculation removes the scalar.

Finally, the rank-transport identity and `rectangularMeasure_zero_rows`
identify the resulting membership with the unchanged canonical zero-row value
set. This proves the generator inclusion and hence the Laurent-span inclusion.

## Provenance and scope

This is an internal composition of the published Library constructions and the
five retained propositions. It introduces no additional source theorem and
proves none of those prerequisites. Its result is conditional and does not
supply the closed intermediate-tail span theorem. Worker 318 authored the
assembly implementation; Worker 829 authored the zero-row and integral
adapters used here. Worker 356 prepared these pairs for this proof task and
revised the documentation to describe the implemented conditional proof.
