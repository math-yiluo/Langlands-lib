# The complete representation operation target

Worker 85 proves the existing Library proposition
`Langlands.Weil.RepresentationOperations.{uG,uV,uU,uT}` from
`Langlands.Weil.Representation.Operations`. The closing theorem is
`Langlands.Weil.representationOperations`, and its type is exactly that
proposition. The group universe `uG` and the three carrier universes `uV`,
`uU` and `uT` stay independent. The statement in `Operations.lean`, its
Markdown, and every imported Lean/Markdown pair are unchanged.

## Implemented proof

`RepresentationOperations` is defined as the conjunction of five published
propositions. The proof is a single anonymous constructor for that
right-nested conjunction. Its five entries are the already published closing
theorems, in the same order as the clauses:

| Clause | Closing theorem used | Module |
| --- | --- | --- |
| `RepresentationIsomorphismInvariance.{uG,uV,uU}` | `representationIsomorphismInvariance.{uG,uV,uU}` | `Langlands.Weil.Representation.IsomorphismInvarianceProof` |
| `RepresentationRankDeterminant.{uG,uV,uU}` | `representationRankDeterminant.{uG,uV,uU}` | `Langlands.Weil.Representation.RankDeterminantProof` |
| `RepresentationExactSequenceInvariants.{uG,uV,uU,uT}` | `representationExactSequenceInvariants.{uG,uV,uU,uT}` | `Langlands.Weil.Representation.ExactSequenceProof` |
| `RepresentationOperationClosure.{uG,uV,uU}` | `representationOperationClosure.{uG,uV,uU}` | `Langlands.Weil.Representation.OperationClosureProof` |
| `RepresentationCharacterNormalization.{uG,uV}` | `representationCharacterNormalization.{uG,uV}` | `Langlands.Weil.Representation.CharacterNormalizationProof` |

Each entry is written with explicit universe arguments that match the
universes the aggregate passes to that clause. The third carrier universe
`uT` occurs only in the exact-sequence clause, and the character-normalization
clause uses only `uG` and `uV`. Every component closing theorem has as its
type the unapplied published proposition, with all carriers, instances,
topologies and hypotheses quantified inside it. The aggregate therefore
gains no hypotheses, witnesses or weakened clauses. No tactic, rewriting or
unfolding is needed beyond the conjunction constructor.

The module only imports the five published proof modules. Each of them
imports `Langlands.Weil.Representation.Operations`. It defines no new
mathematical objects and no auxiliary lemmas.

## Provenance

This is an internal, derived packaging proof, not a new literature theorem.
The mathematics is in the component proofs, which are cited here as
published Library results:

- Worker 16, isomorphism invariance (`IsomorphismInvarianceProof`).
- Worker 4, rank and determinant formulas, rechecked by Worker 69
  (`RankDeterminantProof`).
- Worker 48 with Worker 4, exact-sequence rank additivity and determinant
  multiplicativity (`ExactSequenceProof`).
- Worker 62, operation closure (`OperationClosureProof`).
- Worker 6, determinant character and rank-one normalization
  (`CharacterNormalizationProof`).

Worker 25 stated the target family. Its literature correspondence, to Tate's
*Number theoretic background* (Corvallis 1979, section 2) and Henniart 2002
(sections 2.1–2.2), is recorded in `Operations.md` and is not changed here.
No unpublished proof material was reused.

## Scope

The aggregate is a reusable interface for representations of an arbitrary
group. It is not local reciprocity or the local Langlands correspondence, and
it is not the separate `RepresentationStructure` aggregate. It changes no
twist-class or unramified-twist declarations.
