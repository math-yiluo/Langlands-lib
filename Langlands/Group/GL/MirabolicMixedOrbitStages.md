# Mixed orbit stabilizer containment in stages

This module gives a continuous inclusion of the actual successor section in
its stabilizer, and proves that each of the two left and two right mixed-orbit
stabilizers lies in its actual stages subgroup. All algebraic declarations
hold over every commutative ring `R : Type u`, for all natural `k,r`, including
zero. The section inclusion is continuous for every topology on `R`.

This is a focused internal algebra helper for the BZ77 4.13(b,c) proof. It
establishes no concrete lower-rank section identification, orbit enumeration,
character matching, localization, induction comparison or derivative theorem.
Those are separate obligations of the host task.

## Provenance and conventions

The registered original is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 4.12(II),(III), printed pp.456–458 (PDF pp.17–19), gives the mixed
subgroups. Section 7.2, printed p.471 (PDF p.32), supplies their two
representatives relative to `Q=P_(n-1)V_n`. The published orbit data implements
those actual subgroups and descending permutation matrices, with the cycle
first and the identity second. This module proves new internal matrix and
subgroup identities about that data; it does not assume the source's orbit or
representation comparison conclusions. The original diagrams and cycle
formulas were visually checked during the host development. A bounded project
and literature search found no BZ77-specific erratum; this is not a global
absence assertion.

The Library index `mirabolic s R` denotes the source's `P_(s+1)`. For the
concrete calculations, put `t=k+r+1`. The ambient group is `mirabolic (t+1) R`,
`Q=plusSubgroup t R`, and the actual section is `plusSuccessor`. The subgroup
`sectionSubgroup H w` is the stabilizer preimage along this section;
`stagesSubgroup H w` is its preimage along `plusProjection`. The stabilizer
condition is exactly `w⁻¹*q*w ∈ H`. The coordinate transport in the inducing
subgroups is the published `rankCast (totalRank_eq k r)`.

## Implemented proof

The homomorphism `levi ∘ projection` clears the final translation column of a
mirabolic matrix and preserves all earlier columns. The private
`levi_projection_first` proves this entry identity, including the final row.
`rankCast_symm_levi_projection` shows that clearing commutes with inverse rank
transport by eliminating the equality of ranks and checking matrix entries.
The radical-times-Levi decomposition proves
`eq_levi_projection_of_lastColumn_eq_zero`: a zero final translation column
means the element already equals its cleared form.

The lower-left zero equations defining `leftSubgroup k r R` use only earlier
columns, so clearing preserves them. For `rightSubgroup k r R` the earlier
columns are preserved and the required entries in the final column become
zero. These calculations prove `levi_projection_mem_leftSubgroup` and
`levi_projection_mem_rightSubgroup` from the actual entrywise membership
criteria; no extra subgroup-invariance hypothesis is assumed in the concrete
results.

`sectionInclusion H w` is the actual `plusSuccessor` homomorphism restricted
to its stabilizer preimage. Its value law states equality to `successor g.val`
in the ambient mirabolic group. Its continuity follows from the published
continuous successor map and the induced subgroup topologies; no continuity
of ring operations is needed here.

The generic `orbitStabilizer_le_stagesSubgroup` assumes that clearing preserves
`H` and that clearing fixes `w`. Apply clearing to the actual condition
`w⁻¹*q*w ∈ H`. Since clearing is a group homomorphism and fixes `w`, the result
is `w⁻¹*levi(projection q)*w ∈ H`. For `q∈Q`, this middle factor is exactly
`successor(plusProjection q)`, which is stages membership. These hypotheses
are explicit only in the generic lemma and are proved in full for every
concrete instance below.

Both published representatives have zero final translation column. For the
cycle, the final column is the last standard basis vector; for the identity,
the published `lastColumn_one` applies. This proves
`leftRepresentative_levi_projection` and
`rightRepresentative_levi_projection` for every `i : Fin 2`. Finally,
`leftStabilizer_le_stages` and `rightStabilizer_le_stages` instantiate the
generic lemma. Clearing invariance of each transported inducing subgroup
follows from its actual rank transport and the two mixed-subgroup laws above.
No boundary case introduces a fictitious `P_0` or a representation hypothesis.

## Proof-dependency and inherited restriction audit

There is one direct import:
`Langlands.Group.GL.MirabolicMixedOrbitData`. Its concrete algebra is
published; no orbit theorem or derivative comparison is obtained by
unfolding its definitions. All direct and transitive mathematical proof
inputs here are the radical-times-Levi matrix decomposition,
Levi and projection homomorphism laws, mixed-subgroup entry criteria,
rank reindexing, actual successor continuity, induced subgroup topologies,
subtype and group extensionality, and elementary finite-index arithmetic.
The `omega` uses prove only these finite-index arithmetic facts.

The complete closure below has 21 project imports. Its seven representation
modules are definition modules imported by the generic stabilizer data.
`ClosedSubgroupDefinitions` supplies the actual stabilizer and its
`stabilizerToInducing` homomorphism; no geometric-lemma proof, filtration
comparison, exactness or induction theorem is used. The other representation
modules supply types and ordinary constructions, with no role in the
matrix proofs. The local-field and topology modules are incidental:
the new declarations quantify a commutative ring, and the sole continuity
lemma allows every topology on it without choosing a field topology.

The following rows cover every host restriction directly and transitively;
all references to excluded results include their mathematical conclusions,
parent tasks, proof successors and downstream consequences.

| Host condition or excluded family | Audit of the implemented proof and its complete closure |
| --- | --- |
| Actual coefficients, ranks and both representatives | The inclusions use the actual section, stabilizers and stages, with the proved `totalRank_eq` transport. Both concrete clearing hypotheses are discharged for every representative. The cycle orientation and order remain unchanged. |
| Arbitrary inputs, universes and topology | The algebra holds over any `R : Type u` with `[CommRing R]`, for all `k,r`. The continuity lemma permits every topology. It assumes no representation, admissibility, irreducibility, finite dimension, finite length, genericity or unit vector. It therefore imposes no restriction on the host's independent `uF,uV`, supplied `T`, zero objects, repeated factors or full GL₀ output carrier. |
| Plus functors and adjunction | No plus functor or adjunction module or theorem is imported or used. `plusSubgroup` is permitted matrix-group infrastructure in the orbit data. |
| BZ77 4.13(d) and general Leibniz | No submodule-detection theorem, general Leibniz proof or derivative filtration supplies an input. `Filtration.Definitions` supplies only definitions. |
| Orbit and representation comparisons | No coverage, disjointness, openness, character identity, normalization, Haar scaling, induction comparison or exactness assertion is assumed. This helper proves none of the six host compatibilities by itself. |
| Segment derivative and Jacquet formulas | No segment derivative formula, Ze80 §3.5 or §9.6, `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula` or `SegmentSpecialJacquetExponentNormFormula` is imported or used. |
| Individual segment existence | No individual special-head/reverse-socle or segment-socle/reverse-head existence supplies an input. |
| Linked and unlinked socle consumers | `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`, `JuxtaposedSegmentSocleReverseProductStructure` and `LinkedSegmentSocleReverseProductQuotientHom` supply no input. |
| Segment product, commutation and gluing consumers | No `SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing` or Ze80 4.2 or 9.7 criterion supplies an input. |
| Special-head criterion and generic uniqueness | No `SegmentHeadProductIrreducibility` or `GenericSegmentProductUniqueness` conclusion is used. |
| Ordered existence and multisegment exhaustion | No `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`, ordered strong-head existence, special-head multisegment exhaustion, quotient coverage or ordered conversion supplies an input. |
| Analytic, tempered and square-integrable classification | No analytic segment classification, `SegmentSpecialEssentialSquareIntegrability`, tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable or regular exhaustion, or Ze80 9.3 conclusion is used. |
| Two-supercuspidal consumers | Neither `TwoSupercuspidalNonadjacentProductIrreducible` nor `TwoSupercuspidalProductStructure` or its full-product assembly supplies an input. No parent six-statement conclusion (b),(d),(e),(f) supplies an input. |
| Supercuspidal and single-block finiteness | No `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`, all-character single-block conclusion or arbitrary-character finiteness theorem is imported or used. |
| Other Whittaker finiteness exclusions | `IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement` and the prohibited mirabolic finite-length route through that finiteness are absent from the proof dependencies and the complete import closure. |
| Published-input requirement | The only project root is the published concrete orbit-data module. Imported proposition definitions, citations and pending proofs are not used as proofs. No consumer conclusion supplies an upstream premise. |
| Separate owners and run controls | These matrix calculations do not duplicate restriction-sequence or exactness owners. Worker 127's operator pause, Worker 8's suspension and Worker 114's hold supply no input or waived obligation. |

An import traversal against the audited Library base
`4bec44eec4c7f23def3d25d5c43f4f2a034af469` found exactly the 21 project
imports below. Every imported Lean/Markdown pair was byte-compared with
that Library and its manifest; all pairs agree. Searches for all 38 task
identifiers in the host's inherited exclusion union and the 24 named
consumer declarations found no occurrence in Lean code. The imported orbit
data's Markdown mentions three excluded consumer names solely in its own
independence explanation. Such prose is not a mathematical dependency.
The source scan also found no proof holes, new axioms or unsafe evaluation
commands. Development inspection of `rightStabilizer_le_stages`
reported only the standard `propext`, `Classical.choice` and `Quot.sound`.
These development checks are not independent acceptance or publication.

## Complete project import closure

The list includes the sole direct root and every transitive project
import, excluding this module. Mathlib dependencies use the supplied,
pinned environment; no Mathlib source was modified.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Induction.Definitions
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Twist.Definitions
```
