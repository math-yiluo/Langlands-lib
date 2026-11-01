# Empty natural representation filtrations

Author: Worker 593.

This internal construction uses the published definitions of actual
representation subfunctors, their finite natural filtrations and the actual
zero subfunctor. It applies to any commutative coefficient ring, acting monoid,
source category and independent universes. It assumes no representation
finiteness condition.

`RepFunctorFiltration.zeroLength F h` takes explicit proofs that every carrier
of `F` is a subsingleton. It gives the length-zero flag whose sole step is the
actual zero subfunctor of `F`. Original functor maps preserve zero. Its initial
endpoint is zero by definition; its final endpoint is full because every
ambient vector equals zero. There are no graded indices.

Conversely, `subsingleton_of_zeroLength` uses the two endpoint equations of a
supplied length-zero flag to identify the zero and full subrepresentations
at each object. Every ambient vector therefore equals zero.

`hasOrderedFiltration_empty` and `isGluedFrom_empty` package the constructed
flag for any family indexed by `Fin 0`; the permutation is the identity.
`isGluedFrom_empty_iff` records the converse, and
`isGluedFrom_of_length_eq_zero` also accepts a family length propositionally
equal to zero. No zero or repeated grade at a nonempty index is removed.

This is derived internal content, proved directly from the Library
definitions. No assertion about derivatives, mixed products or Leibniz
filtrations is assumed or established here. The intended application is
the empty quotient block after a separately proved vanishing result.


## Direct and transitive dependencies

The sole direct project import is `Filtration.OneStep`. The complete project
closure has four modules, including this new entry. Every imported Lean and
Markdown pair matches Library commit
`3556873fa475ebf7c4932f5d037eb3dea71c4ddb`; all paired Markdown is nonempty.
No existing Library pair is modified.

| Module under `Langlands.Representation.Filtration` | Role in this proof |
| --- | --- |
| `ZeroLength` | New flag and existence/converse lemmas. |
| `OneStep` | Supplies `RepSubfunctor.zero`, with its proved map-preservation law. Its singleton construction is not used here. |
| `QuotientFirstIso` | Transitive import of `OneStep`; its quotient isomorphism theorems do not enter the new proof. |
| `Definitions` | Actual subfunctors, actual flags with endpoint equations, and the ordered/unordered filtration predicates. |

The proof additionally uses ordinary order laws, equality substitution,
`Subsingleton.elim`, `Fin.elim0` and the identity equivalence from pinned
Mathlib/Lean. The original zero-subfunctor map law is the elementary equation
that a linear map sends zero to zero. No kernel, quotient-isomorphism,
induction, restriction, tensor or exactness assertion is invoked by the new
proofs. Independent coefficient, group, carrier, object and morphism universes
are retained. The new definition takes the objectwise zero-carrier evidence
explicitly and does not manufacture a vanishing theorem.

## Inherited independence audit

This helper is within Worker 593's unchanged all-rank Leibniz task. Every
inherited exclusion continues to apply. The following table checks the
mathematical dependencies, separately from the complete import inventory.
Since the only mathematical input is that a subsingleton module has zero
as every element, no excluded representation-theoretic conclusion or its
successor or downstream consequence occurs as an input.

| Inherited restriction | Check against the implemented argument |
| --- | --- |
| Unlinked/linked/juxtaposed segment-socle pair results, pair reducibility and reverse quotient homomorphisms | No segment object, product theorem, reducibility assertion or quotient-hom existence theorem occurs. Only the zero subfunctor of an arbitrary functor is constructed. |
| SegmentSocleProductIrreducibility; adjacent and two-segment socle commutation; LinkedSegmentSocleGluing | No commutation, gluing-of-segments or irreducibility premise occurs. The generic empty gluing predicate is witnessed directly by its actual zero flag. |
| Individual special-head/reverse-socle and segment-socle/reverse-head existence; ordered multisegment socle existence and socle exhaustion | No segment, head, socle, multisegment or existence/exhaustion result is imported or used. |
| GenericSegmentProductUniqueness; multisegment special-head exhaustion; ordered strong-head existence; quotient coverage; ordered conversion | No uniqueness, coverage, conversion or strong-head assertion is used. The only equivalence introduced is the identity on `Fin 0`. |
| Tempered uniqueness, square-integrable Langlands classification, square-integrable/regular exhaustion, analytic segment classification and forward special square-integrability | No analytic, classification, tempered or square-integrable construction occurs in the complete closure or proof. |
| SegmentHeadProductIrreducibility and special-head criteria | No special-head criterion or representation irreducibility conclusion is used. |
| TwoSupercuspidalNonadjacentProductIrreducible and TwoSupercuspidalProductStructure, including their full-product proof/assembly | No cuspidality, supercuspidality or product theorem is used. |
| Every segment derivative formula and segment-socle/head existence or Jacquet formula, including the parent's (b), (d), (e), (f) | No derivative or Jacquet construction or formula occurs. The helper works for any monoid and coefficient commutative ring. |
| SegmentFullJacquetFormula, SegmentHeadJacquetFormula, SegmentSocleJacquetFormula and SegmentSpecialJacquetExponentNormFormula, including exact proof successors | These names and conclusions are absent from the complete closure and actual proof inputs. |
| Ze80 segment derivatives in Sections 3.5/9.6, product irreducibility in 4.2/9.7, analytic/square-integrability in 9.3, classification/exhaustion, and circular use of the linked-pair converse | No Ze80 result or representation-theoretic source theorem is used. This is a direct proof from the published algebraic definitions. |
| IrreducibleCoinvariantFinitenessStatement, LeviCuspidalCoinvariantFinitenessStatement, SupercuspidalCoinvariantFinitenessStatement, and the prohibited mirabolic finite-length route | No Whittaker, coinvariant, mirabolic, finite-length or finiteness module occurs. The explicit subsingleton hypothesis is used only for the supplied arbitrary functor, never deduced from these consumers. |
| Unproved BZ77 general derivative inputs, pending tasks, citations, private drafts or conditional consumer assertions as proofs | None is an input. The module establishes only the empty natural flag and its converse; it supplies no mixed derivative, vanishing or all-rank Leibniz assertion. |

The source audit scans the following exact conclusion tokens across every Lean
file in the four-module closure; there are no hits:

- `2e5183b1-01e9-44fb-b26c-f4521a25c7c7`
- `AdjacentUnlinkedSegmentSocleSwap`
- `GenericSegmentProductUniqueness`
- `IrreducibleCoinvariantFinitenessStatement`
- `JuxtaposedSegmentSocleReverseProductStructure`
- `LeviCuspidalCoinvariantFinitenessStatement`
- `LinkedSegmentSocleGluing`
- `LinkedSegmentSoclePairReducible`
- `LinkedSegmentSocleReverseProductQuotientHom`
- `LinkedSegmentSocleReverseProductStructure`
- `MultisegmentSocleExhaustion`
- `OrderedMultisegmentSocleExistence`
- `SegmentFullJacquetFormula`
- `SegmentHeadJacquetFormula`
- `SegmentHeadProductIrreducibility`
- `SegmentSocleJacquetFormula`
- `SegmentSocleProductIrreducibility`
- `SegmentSpecialEssentialSquareIntegrability`
- `SegmentSpecialJacquetExponentNormFormula`
- `SquareIntegrableLanglandsClassification`
- `SupercuspidalCoinvariantFinitenessStatement`
- `SupercuspidalDerivatives`
- `TopDerivativeCoinvariantComparison`
- `TwoSegmentSocleCommutation`
- `TwoSupercuspidalNonadjacentProductIrreducible`
- `TwoSupercuspidalProductStructure`
- `UnlinkedSegmentSocleProductIrreducible`

The corresponding complete inherited task-identifier scan also has no hits:

- `1cb45da2-7007-4351-a694-594fb148b8d1`
- `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`
- `23189526-80b0-4828-a6d4-7ebec2cbeef5`
- `23e98d90-6055-4e35-91a9-b0f5d8a84961`
- `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`
- `2e5183b1-01e9-44fb-b26c-f4521a25c7c7`
- `30341ae4-65f2-4a0e-9283-763db01a409e`
- `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`
- `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`
- `3ff5c8fb-397c-4345-bcb3-5d98a0993d18`
- `426911b4-6620-413f-8065-04b25287f3bd`
- `4ca79bbd-589e-476b-9f65-661e799984b5`
- `52e97845-36bb-457d-b76f-70753334b88c`
- `5428fe2c-013c-482d-aa6e-7df43e7191aa`
- `55ad1e10-62d8-46b7-a081-909ef0056426`
- `5ab445dc-d2b4-4072-80d1-6370870a4a26`
- `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`
- `62de5903-b616-4b5c-88eb-a066b77c5467`
- `66e3b87c-647e-41e4-af18-df4d436765f0`
- `67279e36-f3c2-42e3-9302-11729784042e`
- `6780b79c-9526-46aa-b8b4-00377d68b1ea`
- `7ff2a1e9-89dc-439e-a861-a567b3db92bf`
- `8252833d-c269-41a9-824c-5879e531b23b`
- `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`
- `8fa9f68b-fa1b-431a-97f6-5b163964d1fc`
- `92aea10f-62ac-4e0b-bd4a-9a80909797c5`
- `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`
- `ab61f565-1427-4746-ba77-46097563e962`
- `aca8805b-054f-4d56-8045-12db7f623404`
- `b95105c6-f8bb-4641-ae53-2f49d1e7f034`
- `bf433f0a-921a-428c-b0c0-6475438125ac`
- `c84cd52c-3ff3-4024-be50-8b84dd480888`
- `cd8ab97c-0b78-4bce-97c4-d307a28159a4`
- `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`
- `e3634665-571b-4852-9f4c-bab8a1053434`
- `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`
- `ed48ae06-964c-4c84-9e62-978f5a953ca7`
- `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`

The inventory and scans are reproducible by traversing imports from
`Langlands.Representation.Filtration.ZeroLength` and checking the listed
modules' contents. They supplement the direct proof inspection above; absence
of a name alone is not treated as a mathematical independence argument.

## Provenance and task scope

This is internal elementary algebra: the definition of a length-zero flag
already requires its sole subspace to be both zero and full. The forward
construction and converse prove exactly this equivalence for actual natural
subfunctors. No new claim is attributed to the literature and no original
source theorem is needed for the generality stated here. The intended final
application still requires a separately proved, independently accepted and
published vanishing theorem before this flag can be used for a differentiated
restriction quotient. Acceptance of this pair does not complete that theorem
or `GeneralLinearDerivativeLeibnizFiltrationStatement`.
