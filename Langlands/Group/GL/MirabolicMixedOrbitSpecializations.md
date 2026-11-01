# Mixed mirabolic subgroup specializations

Author: Worker 176.

This internal matrix lemma collection supports the two-orbit proof for the
published mixed mirabolic subgroups. It proves no orbit enumeration. Its only
direct import is `Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement`, whose
data, rank transports, cycle orientation and supplied topology remain unchanged.

For every commutative ring, the left inducing subgroup is characterized by its
entries strictly below the cut `k` in columns at most `k`. Hence its upper-left
projection satisfies that same condition. A block diagonal matrix `levi A`
belongs to this subgroup whenever `A` satisfies that condition.

For the right inducing subgroup, the upper-left projection has zero entries in
rows with index greater than `r` and columns at most `r`. Conversely, this
condition on `A` implies that `levi A` belongs to the right inducing subgroup:
the additional final-column equations hold because the Levi inclusion has zero
final column above its bottom entry.

Both proofs use the published entrywise subgroup criteria and the explicit
`rankCast_symm_apply` formula. The `Fin.cast` maps preserve numeric indices.
The right block's mirabolic coordinates are the first `r+1` coordinates and
the final coordinate; its general-linear block occupies the middle `k+1`
coordinates.

The cycle lemmas compute the last row of the projected descending cycle. It is
the delta row at its starting index. Specializing this formula gives the delta
row at `k` for the left cycle and at `r` for the right cycle. The published
descending cycles are used directly.

This is elementary group and matrix infrastructure, derived internally from
the published concrete data motivated by Bernstein–Zelevinsky (1977), §7.2.
No source assertion, proposition definition or pending orbit proof is used as a
proved input. No representation-theoretic theorem is used.

## Exact mathematical dependencies

The implemented proofs use the following earlier local lemmas and published
matrix laws:

| New lemma | Mathematical inputs |
| --- | --- |
| `mem_leftInducing_iff_lowerLeft` | `mem_leftInducing_iff`, `mem_leftSubgroup_iff_entry`, `rankCast_symm_apply`, `leftIndex_inl_val`, `leftIndex_inr_val`, and finite-index arithmetic. |
| `leftInducing_projection_upperHead` | The preceding characterization and the defining formula `projection_apply`. |
| `levi_mem_leftInducing` | The left characterization, `levi_first`, `levi_bottom`, and a split between the final row and the earlier rows. |
| `rightInducing_projection_upperHead` | `mem_rightSubgroup_iff_entry`, the definitional right subgroup transport, `rankCast_symm_apply`, `rightIndex_middle_val`, `rightIndex_first_val`, and `projection_apply`. |
| `levi_mem_rightInducing` | `mem_rightInducing_iff`, `mem_rightSubgroup_iff_entry`, `rankCast_symm_apply`, the three right-index formulas, `levi_first`, and `levi_last`. |
| `cycleElement_projection_lastRow` | `projection_apply`, `cycleElement_entry`, `descendingCycle_apply_val`, and arithmetic case splitting. |
| The two specialized cycle formulas | The generic cycle formula at the published cuts. |

All these declarations concern literal matrix entries. None uses the orbit
proposition as a theorem, and none proves it by assuming a cover, disjointness or
openness condition. The hypotheses of the Levi lemmas are explicit zero-entry
conditions on an arbitrary input matrix; these are adapters for the general
orbit proof, not extra hypotheses on the final orbit theorem. They are proved
over every commutative ring, with only universe `u` and no topology premise.
Their natural-number parameters have no additional inequalities, so both
boundary cases remain included.

## Import closure and publication provenance

The sole direct project import is
`Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement`. Traversing every
project import edge gives the following 22 imported modules, including that
statement:

- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.Maps`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement`
- `Langlands.Group.GL.MirabolicMixedOrbitData`
- `Langlands.Group.GL.MirabolicMixedProductSubgroups`
- `Langlands.Group.GL.MirabolicProjection`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.RankReindex`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Filtration.Definitions`
- `Langlands.Representation.Geometric.ClosedSubgroupDefinitions`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Twist.Definitions`

All 44 Lean/Markdown files were compared byte for byte with Library base
`3556873fa475ebf7c4932f5d037eb3dea71c4ddb` and are unchanged. The new helper
pair imports no additional project module. The inherited Mathlib imports
provide matrix units, finite indices, elementary algebra and topology, and
representation constructions; no excluded project result is introduced by a
new import. The proof expressions listed above use only the matrix and finite
index portion of this closure.

The reused concrete data are independently accepted and public as artifact
`be811761-1085-4fba-8931-e8373301a79a`, with Reviewer 5990's unqualified approval
and integration `cdad94e3ebe84b1198b36da0c5b33e0a` at Library commit
`9a8ca758097242bde4147f33304f43fceef22fa4`. The target statement is independently
accepted and public as `ae87c841-9e57-4c20-b93d-864e6f773693`, with Reviewer 6248's
unqualified approval and integration `b80825d95ab743ddad788cba6b82a9e4` at commit
`5c739daf70eeb88f11ce9139aeb3ed04904874ca`. Their complete independent reviews
were read. Their audits identify the inherited closure as elementary
matrix/local-field constructions and representation definitions, without any
of the excluded mathematical conclusions. The data's author annotation about
permutation orientation was explicitly resolved by its independent reviewer.
The new cycle-row formulas formalize the relevant matrix computation directly.
Neither data acceptance nor statement acceptance is used as an orbit theorem.

## Audit against the complete inherited exclusions

The checks below cover mathematical conclusions, proof successors and
transitive dependents as well as the named modules/tasks. No theorem proving
any excluded conclusion is imported or used. The helper proofs have exactly the
matrix-entry dependencies listed above; no consumer premise supplies an
upstream input.

1. **Plus functors and compatibility.** No plus functor, adjunction, BZ77
   4.13(d), general Leibniz proof or derivative compatibility is imported.
   `plusSubgroup` and its elementary matrix maps occur as permitted group
   infrastructure. No derivative functor module is in the closure, and no
   BZ77 derivative conclusion is assumed.
2. **Geometric and analytic comparisons.** No geometric-lemma proof,
   restriction-sequence theorem, exactness, character matching,
   stabilizer-to-stages containment, Haar scaling, integration or induction
   comparison is used. The imported support and induction definitions are
   constructions, not proofs of those comparisons.
3. **Whittaker finiteness.** No `Langlands.Whittaker` module is imported.
   In particular the closure avoids
   `SupercuspidalCoinvariantFinitenessStatement`
   (`62de5903-b616-4b5c-88eb-a066b77c5467`),
   `IrreducibleCoinvariantFinitenessStatement`
   (`5ab445dc-d2b4-4072-80d1-6370870a4a26`),
   `LeviCuspidalCoinvariantFinitenessStatement`
   (`3ff5c8fb-397c-4345-bcb3-5d98a0993d18`) and the dependent finite-length
   route `5428fe2c-013c-482d-aa6e-7df43e7191aa`. No arbitrary-character or
   degenerate-character finiteness conclusion is used.
4. **Segment-pair structure, commutation and gluing.** The closure has no
   segment, head, socle or Jacquet module. It avoids
   `UnlinkedSegmentSocleProductIrreducible`
   (`23e98d90-6055-4e35-91a9-b0f5d8a84961`),
   `LinkedSegmentSocleReverseProductStructure`
   (`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`),
   `LinkedSegmentSoclePairReducible`
   (`8fa9f68b-fa1b-431a-97f6-5b163964d1fc`),
   `JuxtaposedSegmentSocleReverseProductStructure` and
   `LinkedSegmentSocleReverseProductQuotientHom`
   (`7ff2a1e9-89dc-439e-a861-a567b3db92bf`),
   `SegmentSocleProductIrreducibility`
   (`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`),
   `AdjacentUnlinkedSegmentSocleSwap`
   (`e3634665-571b-4852-9f4c-bab8a1053434`,
   `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`),
   `TwoSegmentSocleCommutation`
   (`426911b4-6620-413f-8065-04b25287f3bd`,
   `66e3b87c-647e-41e4-af18-df4d436765f0`) and
   `LinkedSegmentSocleGluing`
   (`c84cd52c-3ff3-4024-be50-8b84dd480888`,
   `6780b79c-9526-46aa-b8b4-00377d68b1ea`).
5. **Individual and ordered existence, criteria and exhaustion.** The same
   closure avoids individual special-head/reverse-socle existence
   (`67279e36-f3c2-42e3-9302-11729784042e`), individual
   segment-socle/reverse-head existence
   (`4ca79bbd-589e-476b-9f65-661e799984b5`),
   `OrderedMultisegmentSocleExistence`
   (`23189526-80b0-4828-a6d4-7ebec2cbeef5`), socle exhaustion
   (`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`),
   `SegmentHeadProductIrreducibility`
   (`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`),
   `GenericSegmentProductUniqueness`
   (`30341ae4-65f2-4a0e-9283-763db01a409e`), multisegment special-head
   exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head
   existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), quotient coverage
   (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`) and ordered conversion
   (`8252833d-c269-41a9-824c-5879e531b23b`).
6. **Classification and square integrability.** No classification module
   is imported. The closure avoids analytic segment classification
   (`aca8805b-054f-4d56-8045-12db7f623404`),
   `SegmentSpecialEssentialSquareIntegrability`
   (`5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`), tempered uniqueness
   (`52e97845-36bb-457d-b76f-70753334b88c`),
   `SquareIntegrableLanglandsClassification`
   (`1cb45da2-7007-4351-a694-594fb148b8d1`), square-integrable exhaustion
   (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`) and regular exhaustion
   (`bf433f0a-921a-428c-b0c0-6475438125ac`).
7. **Segment derivatives, Jacquet formulas and Ze80.** No segment derivative
   formula, segment existence/Jacquet formula, or segment classification is
   used, including parts (b),(d),(e),(f) of the inherited six-statement
   contribution. The closure avoids `SegmentFullJacquetFormula`
   (`ed48ae06-964c-4c84-9e62-978f5a953ca7`),
   `SegmentHeadJacquetFormula`
   (`55ad1e10-62d8-46b7-a081-909ef0056426`),
   `SegmentSocleJacquetFormula`
   (`b95105c6-f8bb-4641-ae53-2f49d1e7f034`) and
   `SegmentSpecialJacquetExponentNormFormula`
   (`92aea10f-62ac-4e0b-bd4a-9a80909797c5`).
   Ze80 §§3.5, 9.6, Theorems 4.2, 9.3, 9.7 and classification/exhaustion
   results are not used.
8. **Two-supercuspidal conclusions.** No supercuspidal theorem is imported.
   The closure avoids `TwoSupercuspidalNonadjacentProductIrreducible`
   (`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`) and
   `TwoSupercuspidalProductStructure`
   (`ab61f565-1427-4746-ba77-46097563e962`).
9. **Dependency and control boundaries.** Pending statements, citations,
   conditional assemblies and proof tasks are not proved orbit inputs.
   Missing derivative or tensor inputs are not replaced by assumptions
   from consumers. The inherited operator pause of Worker 127, suspension
   of Worker 8 and hold of Worker 114 remain intact; this work grants no
   authority to resume them. No contact with Worker 127 was made.

The complete inherited exclusion union applies to every helper and its
transitive mathematical dependencies. In particular, the statements imported
for types are not theorem assumptions, and no proof successor or downstream
consequence from an excluded family is used to justify a matrix law.

## Development validation

The complete helper module compiled in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; diagnostic
`8321ddfe-b3e5-4824-9c71-c0e6fa511251` reports zero errors and zero warnings.
This is development evidence. The helper pair is intended to be included in
the exact orbit-proof candidate and has not independently supplied the final
coverage theorem. Independent semantic review and publication remain required.
