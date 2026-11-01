# Actual mixed-orbit section coefficient homomorphisms

Author: Worker 499.

This module restricts the actual mixed-orbit coefficient homomorphisms along
the successor sections and computes three complete coefficient pairs. Its
algebraic definitions and identities hold for every commutative ring
`R : Type u` and all natural `k,r`, including zero. The continuity results
add `[TopologicalSpace R] [IsTopologicalRing R]`.

For a section element `g`, write `h` for its image under the actual lower
section equivalence named in the second column. The formulas are:

| Actual coefficient map | Lower section coordinates `h` | Complete pair |
| --- | --- | --- |
| `leftSectionCoefficient k r R 1` | `leftIdentitySectionEquiv k r R g` in `leftSubgroup (k+1) r R` | `((leftProjection h).1, successor (leftProjection h).2)` |
| `rightSectionCoefficient k r R 0` | `rightCycleSectionEquiv k r R g` in `rightSubgroup (k+1) r R` | `(successor (rightProjection h).1, (rightProjection h).2)` |
| `rightSectionCoefficient k r R 1` | `rightIdentitySectionEquiv k r R g` in `leftSubgroup (r+1) k R` | `(levi (leftProjection h).1, (leftProjection h).2.val)` |

These are equalities in the actual upper coefficient groups
`GL_(k+1)(R) × mirabolic (r+1) R` on the left, and
`mirabolic (r+1) R × GL_(k+1)(R)` on the right. The last component in the
last row is the entire underlying general-linear element of
`mirabolic k R`. It is the subgroup inclusion needed for restriction of a
GL representation to the mirabolic group; it is not replaced by a unit.

The pointwise formulas are `leftSectionCoefficient_one`,
`rightSectionCoefficient_zero`, and `rightSectionCoefficient_one` in
namespace `Langlands.GeneralLinear.Mirabolic.MixedOrbit`. Their `_hom`
corollaries assert equality of the corresponding monoid homomorphisms.
No coefficient space or group is replaced by an arbitrarily isomorphic one.

The section prerequisite is independently accepted and published, and the
complete import closure agrees with the published Library as audited below.
This module asserts no orbit enumeration, character comparison,
localization equivalence, normalized representation comparison or host
compatibility theorem.

## Provenance and conventions

The registered original is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 4.12(II),(III), printed pp.456–458 (PDF pp.17–19), specifies the
mixed subgroup diagrams. Section 7.2, printed p.471 (PDF p.32), supplies
the descending cycles for 4.13(b,c). The original diagrams and cycle page
image were visually read during the host development. A bounded project
and literature errata search found no BZ77-specific entry; this is no
global absence assertion.

The explicit coefficient identities here are internal derived content.
They follow from the actual maps in `MirabolicMixedOrbitData` and the
actual lower equivalences in `MirabolicMixedOrbitSections`. The proof
computes entries of those maps and does not assume BZ77's representation
comparison conclusions.

Set `t=k+r+1`. The ambient group is `mirabolic (t+1) R`, and a successor
section element lies in `mirabolic t R`. The inducing source has GL rank
`k+1` and mirabolic group `mirabolic (r+1) R = P_(r+2)`. Representative
`0 : Fin 2` is the descending cycle and `1` is the identity. The
coefficient convention is inverse conjugation `w⁻¹ * successor(g) * w`,
followed by the inverse of `rankCast (totalRank_eq k r)` and the actual
mixed block projection. Each lower equivalence is itself the inverse rank
cast restricted to the proved section subgroup. No rank transport is
suppressed in the Lean definitions or identities.

On the right the descending cycle sends zero-based coordinate `r` to `t`
and each `r<j≤t` to `j-1`; it fixes the ambient final coordinate `t+1`.
The lower right mirabolic block consists of the first `r` coordinates and
the lower final coordinate `t`. The lower right GL block consists of the
middle `k+1` coordinates. At the right identity, the lower left GL block
has size `r+1` and the remaining lower mirabolic block is `mirabolic k R`.
This is the reversal of block roles already proved by the actual section
equivalence, not an assumed interchange of the coefficient inputs.

All ranks permit `k=0` and `r=0`. In particular, `mirabolic 0 R` is `P_1`.
No `P_0` is introduced, and this algebraic helper imposes no condition on
the host's arbitrary representation carriers, independent carrier universe
or entire GL₀ output carrier.

## Implemented proof

`leftSectionCoefficient i` is exactly

```text
(leftCoefficient k r R i).comp (plusSuccessor.subgroupComap _).
```

Its domain is the actual comap subgroup `leftSection k r R i`.
`rightSectionCoefficient` is defined in the same way from
`rightCoefficient`. Membership in the target stabilizer is supplied by the
comap itself. No auxiliary subgroup-correspondence premise is added.

The private `successor_entry_eq` compares a successor entry with a lower
entry when the two row and column values agree; `Fin.ext` identifies the
upper indices with the lower `castSucc` indices, and `successor_first`
finishes the calculation. `successor_last_eq` similarly proves the zero
upper final-column entries for every nonfinal row. These are elementary
entry tools, not alternative definitions of the successor.

For `leftSectionCoefficient_one`, product, subgroup, unit and matrix
extensionality reduce the complete pair to entries. The actual published
coefficient entry laws remove identity conjugation. The first component
is the upper left GL block; the rank casts and lower projection have the
same numerical indices, so `successor_entry_eq` proves equality. For the
mirabolic component, `Fin.lastCases` separates the final row and column.
Their final/final entry is one and their mixed entries are zero by the
actual successor's last row and `successor_last`. All earlier entries
reduce to the lower trailing block by `successor_first`, the lower
projection entry law and `rankCast_symm_apply`.

`rightSectionCoefficient_one` uses the same entrywise route. Its upper
mirabolic block contains the first `r+1` coordinates and the ambient
final coordinate; the latter row and column give precisely the final row
and column of `levi` of the lower GL block. The earlier entries use
`levi_first` and the lower left projection. The upper middle GL block
consists entirely of earlier successor coordinates and agrees with the
entire underlying lower trailing mirabolic block. No entry or GL factor
is discarded.

For `rightSectionCoefficient_zero`, the private four-line
`cycle_inv_conjugate_entry` expands the actual permutation matrices and
applies their multiplication entry formulas. Inverse conjugation reads
the matrix at the descending permutation applied to both indices. This
is the same elementary calculation authored by Worker 499 in the
separate radical and section helpers; no radical helper is imported.

The two private cyclic index lemmas make the actual rank casts explicit.
`rightCycle_upper_first` separates the last index of the first `r+1`
upper coordinates: the first `r` coordinates stay fixed and coordinate
`r` becomes the lower final coordinate `t`. The result is precisely the
`castSucc` of the lower right mirabolic block index.
`rightCycle_upper_middle` sends upper coordinate `r+1+a` to `r+a`,
which is the corresponding lower right GL block index. Both lemmas
prove equality of the actual `Fin` indices, not just a permutation of
abstract block labels. The final ambient coordinate remains fixed by
`descendingCycle_last`.

The complete cyclic coefficient proof then separates the final row and
column using `Fin.lastCases`. The two index lemmas and
`successor_first` identify all earlier entries with the lower right
projection. The final entries are the actual successor's standard final
row and zero final column. Every numerical bound and equality uses
explicit finite-index arithmetic, including the empty-block cases.

The three `_hom` corollaries apply `MonoidHom.ext` to these full-pair
formulas. The postcompositions are respectively `id.prodMap successor`,
`successor.prodMap id`, and `levi.prodMap (mirabolic k R).subtype`.
Each is composed with the actual lower projection and the corresponding
lower section equivalence's `toMonoidHom`.

`continuous_leftSectionCoefficient` and
`continuous_rightSectionCoefficient` hold for all `i : Fin 2`. They
compose the published continuous coefficient maps with the continuous
successor restricted through the induced subgroup topology. These
continuity proofs require a topological ring, as do their published
coefficient-map continuity inputs. The algebraic formulas and homomorphism
equalities impose no topology assumption.

## Proof-dependency and inherited restriction audit

The sole direct project import is
`Langlands.Group.GL.MirabolicMixedOrbitSections`. Its closure contains
22 project modules. The actual mathematical inputs are the lower section
equivalences, coefficient entry laws, successor and Levi entry laws,
explicit permutation matrix entry laws, actual block projections, rank
reindexing, continuous coefficient and successor maps, induced subgroup
topologies and elementary extensionality and finite-index arithmetic.
The `omega` calls prove only those index bounds and equalities.

The seven representation modules in this closure are reached through the
concrete stabilizer definitions in `MirabolicMixedOrbitData`.
`ClosedSubgroupDefinitions` supplies the stabilizer and actual
`stabilizerToInducing` homomorphism; it supplies no geometric-lemma
comparison theorem. The other representation modules give ordinary
constructions and types and have no comparison role in these matrix
proofs. The local-field imports are incidental to this ring-general
helper; no p-adic or canonical topology is chosen.

The following rows cover every host restriction directly and transitively.
Each excluded family includes its mathematical conclusions, parent tasks,
proof successors and downstream consequences.

| Host condition or excluded family | Audit of the implemented proof and its complete closure |
| --- | --- |
| Actual coefficients, ranks and both representatives | The new maps restrict the actual coefficient homomorphisms along the actual successor. All three complete-pair formulas and homomorphism equalities retain inverse rank casts and actual lower subgroup projections. The right identity includes the entire lower mirabolic block into GL. No left cyclic section coefficient formula is claimed here. |
| Arbitrary inputs, universes and topology | The algebra holds over any `R : Type u` with `[CommRing R]`, for all `k,r`. The continuity results require a topological ring; the algebraic formulas require only a commutative ring. It assumes no representation, admissibility, irreducibility, finite dimension, finite length, genericity or unit vector. It therefore imposes no restriction on the host's independent `uF,uV`, supplied `T`, zero objects, repeated factors or full GL₀ output carrier. |
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
| Published-input requirement | The concrete orbit data and lower section equivalences are the only mathematical project inputs. Both are independently accepted and published. Every imported Lean/Markdown pair agrees with the published Library and its manifest. No proposition definition, citation, pending derivative proof or consumer conclusion supplies a premise. |
| Separate owners and run controls | These matrix calculations do not duplicate restriction-sequence or exactness owners. Worker 127's operator pause, Worker 8's suspension and Worker 114's hold supply no input or waived obligation. |


The completed audit against Library base
`8f53f05bb76983088fd64f190658c6ac4c3edc1b` finds exactly the 22 project
imports below. All 22 published Lean/Markdown pairs agree byte for byte
with that Library and its manifest, including the independently accepted
and published section pair. The source scan finds none of
the host's 38 excluded task identifiers or 24 named consumer declarations
in Lean code, and no proof holes, new axioms or unsafe evaluation commands.
Excluded consumer names in imported paired Markdown are explanations of
independence, not proof inputs. Inspection of
`rightSectionCoefficient_one_hom` reports the single ring universe `u` and
only the standard `propext`, `Classical.choice` and `Quot.sound` axioms.
Development compilation is not independent semantic acceptance or publication.

## Complete project import closure

This list includes the sole direct root and every transitive project
import, excluding this module. Mathlib uses the supplied pinned environment;
no Mathlib source was modified.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitSections
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
