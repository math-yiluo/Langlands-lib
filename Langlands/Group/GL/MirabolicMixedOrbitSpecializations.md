# Mixed mirabolic subgroup specializations

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
No source assertion, proposition definition or orbit statement is used as a
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

## Import closure and provenance

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

The reused concrete data (`MirabolicMixedOrbitData`) and the target statement
(`MirabolicMixedOrbitCoverageStatement`) are published Library modules. Their
audits identify the inherited closure as elementary
matrix/local-field constructions and representation definitions, without any
of the excluded mathematical conclusions. The permutation orientation is fixed
and explained in the data module.
The new cycle-row formulas formalize the relevant matrix computation directly.
Neither the data nor the statement is used as an orbit theorem.

## Results not used

The checks below cover mathematical conclusions and their transitive
dependents as well as the named modules. No theorem proving
any excluded conclusion is imported or used. The helper proofs have exactly the
matrix-entry dependencies listed above; no premise of a later result supplies an
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
   `SupercuspidalCoinvariantFinitenessStatement`,
   `IrreducibleCoinvariantFinitenessStatement`,
   `LeviCuspidalCoinvariantFinitenessStatement` and the dependent finite-length
   route. No arbitrary-character or
   degenerate-character finiteness conclusion is used.
4. **Segment-pair structure, commutation and gluing.** The closure has no
   segment, head, socle or Jacquet module. It avoids
   `UnlinkedSegmentSocleProductIrreducible`,
   `LinkedSegmentSocleReverseProductStructure`,
   `LinkedSegmentSoclePairReducible`,
   `JuxtaposedSegmentSocleReverseProductStructure` and
   `LinkedSegmentSocleReverseProductQuotientHom`,
   `SegmentSocleProductIrreducibility`,
   `AdjacentUnlinkedSegmentSocleSwap`,
   `TwoSegmentSocleCommutation` and
   `LinkedSegmentSocleGluing`.
5. **Individual and ordered existence, criteria and exhaustion.** The same
   closure avoids individual special-head/reverse-socle existence, individual
   segment-socle/reverse-head existence,
   `OrderedMultisegmentSocleExistence`, socle exhaustion,
   `SegmentHeadProductIrreducibility`,
   `GenericSegmentProductUniqueness`, multisegment special-head
   exhaustion, ordered strong-head
   existence, quotient coverage and ordered conversion.
6. **Classification and square integrability.** No classification module
   is imported. The closure avoids analytic segment classification,
   `SegmentSpecialEssentialSquareIntegrability`, tempered uniqueness,
   `SquareIntegrableLanglandsClassification`, square-integrable exhaustion
   and regular exhaustion.
7. **Segment derivatives, Jacquet formulas and Ze80.** No segment derivative
   formula, segment existence/Jacquet formula, or segment classification is
   used. The closure avoids `SegmentFullJacquetFormula`,
   `SegmentHeadJacquetFormula`,
   `SegmentSocleJacquetFormula` and
   `SegmentSpecialJacquetExponentNormFormula`.
   Ze80 §§3.5, 9.6, Theorems 4.2, 9.3, 9.7 and classification/exhaustion
   results are not used.
8. **Two-supercuspidal conclusions.** No supercuspidal theorem is imported.
   The closure avoids `TwoSupercuspidalNonadjacentProductIrreducible` and
   `TwoSupercuspidalProductStructure`.
9. **Dependency boundaries.** Unproved statements, citations and
   conditional assemblies are not proved orbit inputs.
   Missing derivative or tensor inputs are not replaced by assumptions
   taken from results that use these lemmas.

These exclusions apply to every helper and its
transitive mathematical dependencies. In particular, the statements imported
for types are not theorem assumptions, and no proof or downstream
consequence from an excluded family is used to justify a matrix law.

## Validation

The complete helper module compiled with Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, with zero errors and zero warnings.
The helper pair does not itself supply the final coverage theorem; that is
`mirabolicMixedOrbitCoverage` in `MirabolicMixedOrbitCoverageProof`, which
imports this module.
