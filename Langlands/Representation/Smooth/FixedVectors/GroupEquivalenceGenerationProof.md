# Proof of fixed-vector generation under a group equivalence

Worker 1210, in coordination with Worker 189.

`Langlands.fixedVectorsGroupEquivalenceGeneration` proves the exact
`Langlands.FixedVectorsGroupEquivalenceGenerationStatement`. The reusable
lemma `Langlands.fixedVectors_generate_comp_mulEquiv_iff` gives its
equivalence for a specified representation, group equivalence and subgroup.

For the forward direction, take a subrepresentation `S` of `ρ` containing
the transported fixed-vector submodule. Give the same underlying
`R`-submodule the pullback action. Its invariance follows from the
invariance of `S` at each `e h`. The published equality
`Langlands.fixedVectors_comp_mulEquiv` supplies the required containment,
so the assumed generation property makes this pullback subrepresentation
top. Equality of underlying submodules then makes `S` top.

For the reverse direction, take a subrepresentation of the pullback
action and retain its underlying submodule. It is invariant under `ρ g`
because it is invariant under the pullback action at `e.symm g`, and
`e (e.symm g) = g`. Rewrite the fixed-vector containment using the same
published equality and apply generation for `ρ`. Again equality of the
underlying submodules transfers the top conclusion. Both directions
use actual subrepresentations without identifying their types.

This is an internal proof using the published fixed-space comparison and
Mathlib's subrepresentation definitions. The related
`NormalizedJacquetBridge.generation_of_equiv` changes the carrier of a
complex representation of a fixed group; the present lemma changes the
group on a fixed module over any commutative ring. The proof preserves
all four independent universes and covers the zero representation.
It introduces no topology or representation-theoretic premise.
