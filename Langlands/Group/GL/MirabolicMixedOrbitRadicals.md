# Radical calculations for mixed mirabolic orbit representatives

This internal helper proves elementary matrix identities for the actual two
representatives in `MirabolicMixedOrbitData`. It identifies their radical
intersections and their coefficient projections, over any commutative ring.
The identities include all nonnegative values of the two rank parameters.
They provide lower algebra for the positive-source-rank Phi comparisons;
this module does not prove those representation comparisons.

## Provenance and conventions

The source is I. N. Bernstein and A. V. Zelevinsky, *Induced representations
of reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, retained PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 4.12(II),(III), printed pp.456–458 (PDF pp.17–19), specifies the
mixed subgroups. Section 7.2, printed p.471 (PDF p.32), specifies the
cycles for the two minus comparisons. The native source page image was
read, including the cycle orientation. A bounded project and literature
errata search found no specific BZ77 errata entry; this asserts no global
absence of errata.

The imported concrete data already implement these subgroups, their block
projections, the descending cycles and the inverse-conjugation convention.
The present column functions and matrix equalities are internal derived
content, proved from those definitions. The source leaves the comparison
details to the reader; no displayed identity here is represented as a
verbatim theorem of the source. Elementary proof patterns also reuse
Worker 499's own earlier mixed-product radical calculations.

In the focused orbit sections, `k r : ℕ` mean GL rank `K=k+1`, source
mirabolic rank `m=r+2` and ambient matrix rank `n=k+r+3`. The ambient
radical has column length `d=k+r+2`. Write `U(v)` for the actual
`radicalElement v`, and put `t=d-1=k+r+1`. Indices below are zero based.
The coefficient radical `U(w)` has column length `r+1` and lies in
`mirabolic (r+1) R`, that is, source `P_(r+2)`.

The rank transport is the actual group equivalence
`rankCast (totalRank_eq k r)` from parameter `k+1+(r+1)` to `d`.
Representatives at index `0 : Fin 2` are descending cycles, and at index
`1` are identities. The inverse conjugation is exactly
`w⁻¹ * U(v) * w`, consistent with the orbit of `H w⁻¹` in the imported
definitions. No orbit enumeration is assumed by these calculations.

## Generic calculations

`cycleRadicalIndex t a` sends the column index `a` to `t`, each index
strictly greater than `a` to its predecessor, and smaller indices to
themselves. When `a≤t`, `descendingCycle_castSucc` identifies this
function with the source cycle on the nonfinal matrix coordinates.
`cycleElement_inv_conjugate_entry` proves the entry identity

```text
(w⁻¹ g w)[i,j] = g[cycle(i),cycle(j)].
```

Permutation multiplication and inversion prove that identity.
`cycleElement_inv_conjugate_radicalElement` then proves
`w⁻¹ U(v) w = U(v ∘ cycleRadicalIndex t a)`. Its proof separates the final
matrix column and row from the first columns; the latter are the identity
matrix. Both `rankCast_radicalElement` and its symmetric version transport
the actual column by the inverse or forward `Fin.cast`, respectively.
Their proofs eliminate the equality of ranks.

The generic mixed-subgroup calculations use arbitrary `k r : ℕ`, before
the focused successor shifts. Every radical of `mirabolic (k+r) R`
belongs to `leftSubgroup k r R`. Its left projection is

```text
(1, U(j ↦ v[k+j]))                 (j : Fin r).
```

Membership in `rightSubgroup k r R` is equivalent to
`v[r+j]=0` for every `j : Fin k`. For any witness of that membership,
the right projection is

```text
(U(j ↦ v[j]), 1)                  (j : Fin r).
```

The theorems are `radicalElement_mem_leftSubgroup`,
`leftProjection_radicalElement`,
`radicalElement_mem_rightSubgroup_iff` and
`rightProjection_radicalElement`. The proofs apply the published entry
criteria, compute the two diagonal blocks and use disjointness of their
index ranges. The GL blocks equal the entire identity, including empty
blocks; no vector-space dimension or nonzero-ring hypothesis is needed.

## Actual left representatives

`leftRadicalColumn` records inverse conjugation and rank transport at
either actual left representative. `left_conjugate_radicalElement`
proves the complete equality of group elements with this column.
Every ambient radical belongs to either actual
`leftRadicalIntersection`; `leftOrbitRadicalElement` packages the
membership proof. Consequently `leftRadicalIntersection_eq_top` proves
that both intersections are the full radical subgroup.

The coefficient is the actual `leftRadicalCoefficient`, which composes
the inclusion into the stabilizer, `stabilizerToInducing`, inverse rank
transport and `leftProjection`. The theorem
`leftRadicalCoefficient_element` computes this entire composition.
Its two specializations give the following exact formulas.

| Representative | Coefficient on `U(v)` |
| --- | --- |
| Cycle (`0`) | `(1, U(j ↦ v[k+j]))`, for `j : Fin (r+1)` |
| Identity (`1`) | `(1, U(j ↦ v[k+1+j]))`, for `j : Fin (r+1)` |

These are `leftRadicalCoefficient_zero` and
`leftRadicalCoefficient_one`. They retain coordinates `k,…,k+r` and
`k+1,…,k+r+1`, respectively. The word "coefficient" here refers to the
homomorphism into the product of matrix groups, before any representation
or character is applied.

`terminalRadicalColumn t c` has value `c` at coordinate `t` and zero
elsewhere. `leftRadicalCoefficient_terminal` proves that the entire
cycle coefficient of this column is `1`, for every `c : R`. The column
retained by the cycle ends at `k+r`, so it is identically zero, and the
GL block is already the identity. This is a matrix identity; this module
draws no character-vanishing or representation-vanishing conclusion.

## Actual right representatives

`rightRadicalColumn` records the analogous cycle or identity column,
with cycle start `r`. `right_conjugate_radicalElement` proves inverse
conjugation followed by the actual rank transport.
`radicalElement_mem_rightRadicalIntersection_iff` reduces intersection
membership to the generic middle-coordinate criterion. Its two
specializations and `rightRadicalCoefficient_zero/one` prove:

| Representative | Necessary and sufficient membership condition | Coefficient on a member `U(v)` |
| --- | --- | --- |
| Cycle (`0`) | `v[r+j]=0` for every `j : Fin (k+1)` | `(U(w),1)`, where `w[j]=v[j]` for `j<r` and `w[r]=v[t]` |
| Identity (`1`) | `v[r+1+j]=0` for every `j : Fin (k+1)` | `(U(j ↦ v[j]),1)`, for `j : Fin (r+1)` |

`rightOrbitRadicalElement` packages an actual membership witness;
`rightRadicalCoefficient_element` first computes the general coefficient
on this element, and the two formulas simplify its column. The right
cycle retains the first `r` ambient coordinates and uses the ambient
terminal coordinate as its own final radical coordinate. The right
identity retains the first `r+1` ambient coordinates.

Finally, `rightRadicalIntersection_one_terminal_zero` substitutes
`Fin.last k` into the identity membership criterion and proves `v[t]=0`.
All formulas include `k=0` and `r=0`. This successor-source helper does
not create `P_0`, apply Phi to `P_1`, or replace any carrier by a chosen
unit representation.

## Proof-dependency and inherited restriction audit

There is one direct import:
`Langlands.Group.GL.MirabolicMixedOrbitData`. Its concrete algebra is
published; no orbit theorem or derivative comparison is obtained by
unfolding its definitions. All direct and transitive mathematical proof
inputs here are permutation-matrix multiplication and inversion,
radical matrix entries, mixed-subgroup entry criteria and block projections,
subtype and group extensionality, and elementary finite-index arithmetic.
The `omega` uses prove only these finite-index arithmetic facts.

The complete closure below has 21 project imports. Its seven representation
modules are definition modules imported by the generic stabilizer data.
`ClosedSubgroupDefinitions` supplies the actual stabilizer and its
`stabilizerToInducing` homomorphism; no geometric-lemma proof, filtration
comparison, exactness or induction theorem is used. The other representation
modules supply types and ordinary constructions, with no role in the
matrix proofs. The local-field and topology modules are incidental:
the new declarations quantify only a commutative ring and never choose a
field topology.

The following rows cover every host restriction directly and transitively;
all references to excluded results include their mathematical conclusions,
parent tasks, proof successors and downstream consequences.

| Host condition or excluded family | Audit of the implemented proof and its complete closure |
| --- | --- |
| Actual coefficients, ranks and both representatives | The equalities use the published groups and homomorphisms themselves, with the proved `totalRank_eq` transport. Membership is proved for the actual intersections. The cycle orientation and order remain unchanged. |
| Arbitrary inputs, universes and topology | The algebra holds over any `R : Type u` with `[CommRing R]`, for all `k,r`. It assumes no representation, topology, admissibility, irreducibility, finite dimension, finite length, genericity or unit vector. It therefore imposes no restriction on the host's independent `uF,uV`, supplied `T`, zero objects, repeated factors or full GL₀ output carrier. |
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
`3556873fa475ebf7c4932f5d037eb3dea71c4ddb` found exactly the 21 project
imports below. Every imported Lean/Markdown pair was byte-compared with
that Library and its manifest; all pairs agree. Searches for all 38 task
identifiers in the host's inherited exclusion union and the 24 named
consumer declarations found no occurrence in Lean code. The imported orbit
data's Markdown mentions three excluded consumer names solely in its own
independence explanation. Such prose is not a mathematical dependency.
The source scan also found no proof holes, new axioms or unsafe evaluation
commands. Development inspection of `leftRadicalCoefficient_terminal`
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
