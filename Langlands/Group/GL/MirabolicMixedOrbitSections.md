# Actual lower-rank mixed-orbit sections

This module constructs three explicit multiplicative equivalences from actual
mixed-orbit successor sections to the expected lower mixed subgroups. All
algebra holds over every commutative ring `R : Type u`, for all natural `k,r`,
including zero. Each equivalence and its inverse are continuous for every
topology on `R`; no continuity of the ring operations is required.

| Actual section in `mirabolic (k+r+1) R` | Lower subgroup | Rank equality used by the forward inverse rank cast |
| --- | --- | --- |
| `leftSection k r R 1` | `leftSubgroup (k+1) r R` | `(k+1)+r = k+r+1` |
| `rightSection k r R 0` | `rightSubgroup (k+1) r R` | `(k+1)+r = k+r+1` |
| `rightSection k r R 1` | `leftSubgroup (r+1) k R` | `(r+1)+k = k+r+1` |

The corresponding definitions are `leftIdentitySectionEquiv`,
`rightCycleSectionEquiv` and `rightIdentitySectionEquiv` in namespace
`Langlands.GeneralLinear.Mirabolic.MixedOrbit`. Each forward map is exactly
the inverse of the published `rankCast` along the displayed equality,
restricted to the actual subgroup. Each inverse is the forward `rankCast`.
These are group equivalences, not merely equalities of isomorphism classes.
The module establishes no coefficient-map identity, left cyclic section
identification, orbit enumeration, character matching, localization,
induction comparison or derivative theorem.

## Provenance and conventions

The registered original is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 4.12(II),(III), printed pp.456–458 (PDF pp.17–19), supplies the mixed
subgroup diagrams. Section 7.2, printed p.471 (PDF p.32), supplies the cyclic
representatives for 4.13(b,c). The actual mixed subgroups, inverse rank
transports and descending permutation matrices already occur in the
published `MirabolicMixedOrbitData`. This module proves internal derived
identifications from those definitions, rather than taking the source's
representation conclusions as proved inputs. The original diagrams and cycle
formulas were visually checked during the host development. A bounded project
and literature search found no BZ77-specific erratum; this is not a global
absence assertion.

The Library's `mirabolic s R` denotes `P_(s+1)`. Set `t=k+r+1`. The ambient
group is `mirabolic (t+1) R`, and the section is the actual successor from
`mirabolic t R` into `plusSubgroup t R`. A section member satisfies
`w⁻¹ * successor(g) * w ∈ H`. The two representatives are the cycle at
index `0` and the identity at index `1`. On the right the cycle sends
`r` to `t` and each `r<j≤t` to `j-1`, fixing all other indices, including
the ambient final coordinate `t+1`. Every subgroup on the right of the table
uses the published concrete block embedding, including the reversed order
in the last row. No fictitious `P_0` occurs: when `r=0`, the smaller mirabolic
block is the actual `mirabolic 0 R = P_1`.

## Implemented proof

The private entry criteria first remove block labels from the published
membership equations. For `g : mirabolic (a+b) R`, left membership is
exactly `g[i,j]=0` whenever `a≤i.val` and `j.val<a`. Right membership is
exactly `g[i,j]=0` whenever `b≤i.val<b+a` and either `j.val<b` or `j` is
the final index. Each implication constructs the corresponding actual
`leftIndex` or `rightIndex`; the final right column is handled separately.
The transported versions eliminate the rank equality and reduce to the same
entry criteria. These criteria are private proof tools, not replacements for
the actual subgroup definitions.

For `mem_leftSection_one_iff`, identity conjugation disappears. The zero
rectangle for `successor(g)` agrees with the lower left zero rectangle by
`successor_first`. The extra final row is the mirabolic final standard
basis row and gives zero in every required earlier column. This proves
both directions without a field or positivity assumption.

For `mem_rightSection_one_iff`, the upper right condition has rows
`r+1≤i.val<k+r+2`, with earlier columns `j.val<r+1` and the ambient final
column. The earlier columns reduce to the lower left zero rectangle with
first-block size `r+1`. The ambient final column is zero above its final
entry by `successor_last`. Conversely every lower row lies in the upper
row range after applying `castSucc`, so the implication also reverses.

For `mem_rightSection_zero_iff`, the private permutation calculation proves
that inverse conjugation by the cycle reads entries at the descending
cycle applied to both indices. Its four-line proof expands the actual
permutation matrices and uses their multiplication entry laws. This same
elementary calculation was authored by Worker 499 in the separate radical
helper; no pending helper is imported here. Rows `r+1,...,k+r+1` map to
`r,...,k+r`. Columns less than `r` stay fixed, column `r` maps to the
lower final index `t`, and the ambient final column remains final and is
zero in the successor. The reverse implication chooses the original row
one larger, and either the same earlier column or column `r`. The finite
bounds, including empty first or middle ranges, are proved explicitly by
`omega`. Thus both directions use the actual cycle, without assuming a
conjugacy or subgroup correspondence hypothesis.

The private `restrictEquiv` restricts an existing multiplicative equivalence
using an explicitly proved membership iff. The three public equivalences
apply it to the inverse rank cast and the three results above. The inverse
laws and multiplication law follow from the original equivalence and
subtype extensionality. The public value lemmas are definitional equalities.
The six continuity lemmas compose the published continuous rank casts with
subtype projections and induced subgroup topology maps. They impose only
`[TopologicalSpace R]` in addition to the commutative ring assumption.

## Proof-dependency and inherited restriction audit

There is one direct import:
`Langlands.Group.GL.MirabolicMixedOrbitData`. Its concrete algebra is
published; no orbit theorem or derivative comparison is obtained by
unfolding its definitions. All direct and transitive mathematical proof
inputs here are the mixed-subgroup matrix-entry criteria, the explicit descending permutation and its matrix,
rank reindexing, successor matrix entries, continuity of rank transport, induced
subgroup topologies, subtype and group extensionality, and elementary
finite-index arithmetic.
The `omega` uses prove only these finite-index arithmetic facts.

The complete closure below has 21 project imports. Its seven representation
modules are definition modules imported by the generic stabilizer data.
`ClosedSubgroupDefinitions` supplies the actual stabilizer and its
`stabilizerToInducing` homomorphism; no geometric-lemma proof, filtration
comparison, exactness or induction theorem is used. The other representation
modules supply types and ordinary constructions, with no role in the
matrix proofs. The local-field and topology modules are incidental:
the new declarations quantify a commutative ring, and all six continuity
lemmas allow every topology on it without choosing a field topology.

The following rows cover every host restriction directly and transitively;
all references to excluded results include their mathematical conclusions,
parent tasks, proof successors and downstream consequences.

| Host condition or excluded family | Audit of the implemented proof and its complete closure |
| --- | --- |
| Actual coefficients, ranks and both representatives | The equivalences use the actual successor sections, inducing subgroups and descending cycle. Every rank equality is proved and every subgroup membership premise is discharged. They identify the left identity, right cyclic and right identity sections; the left cyclic section is not claimed here. Full coefficient maps are a separate obligation. |
| Arbitrary inputs, universes and topology | The algebra holds over any `R : Type u` with `[CommRing R]`, for all `k,r`. The continuity lemmas permit every topology. It assumes no representation, admissibility, irreducibility, finite dimension, finite length, genericity or unit vector. It therefore imposes no restriction on the host's independent `uF,uV`, supplied `T`, zero objects, repeated factors or full GL₀ output carrier. |
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
commands. Development inspection of `rightCycleSectionEquiv`
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
