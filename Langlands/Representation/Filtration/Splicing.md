# Refinement of actual natural representation filtrations

This entry module completes the generic construction of task
`7259c98c-1565-475d-88da-f928adf1f613`, by Worker 187. It imports the actual
short-exact splice from `Filtration.Splicing.Basic` and constructs refinement
of a supplied natural filtration by supplied filtrations of its actual graded
quotient functors. The splice and its complete concatenation interface are
explained in [Splicing/Basic.md](Splicing/Basic.md).

Let `M : C ⥤ Rep R G`, where `R` is a commutative ring, `G` is a monoid and
`C` is a category. The ring, monoid, carrier, source-object and source-morphism
universes `uR`, `uG`, `uV`, `uC`, `vC` are independent. In particular the
construction applies with carrier universe `max uF uV` and imposes no
universe-saturation condition. Let `s : RepFunctorFiltration M n`,
`m : Fin n → ℕ`, and
`inner i : RepFunctorFiltration (s.graded i) (m i)` be supplied actual data.
Here every `graded` is the quotient of the actual upper subfunctor by the
inverse image of the actual lower subfunctor.

`RepFunctorFiltration.refine s m inner` is actual filtration data of `M` of
length `∑ i, m i`. No finite length, smoothness, dimension, simplicity or
nonzero assumption occurs. `refineGradedIso` gives a natural isomorphism from
its grade at `flattenIndex m i j` to exactly `(inner i).graded j`.
`refineGradedIsoAt` gives the comparison at an arbitrary flattened index.

For a filtration of length `n+1`, `penultimate` is its step at value `n`.
`initialFiltration` pulls the first `n+1` steps back along the canonical
inclusion of that subfunctor. Monotonicity is inherited. Its zero endpoint
uses injectivity of subtype inclusion, and its full endpoint is the whole
penultimate subfunctor. `prefixGradedIso` identifies all its first `n` grades
naturally with the original grades at `i.castSucc`.

The auxiliary comparison
`RepSubfunctor.inverseImageQuotientIsoOfUpperSurjective` requires surjectivity
only onto the given upper step. It restricts the ambient natural map to that
step and composes with the actual quotient projection. The kernel condition
is membership in the inverse image of the lower step, and representatives
give surjectivity. It then reuses the published natural quotient first
isomorphism. For `prefixGradedIso`, the upper step lies in the penultimate
step by monotonicity, so each upper vector lifts to the restricted source.
The result is an isomorphism of actual quotient functors, with naturality
in every source morphism.

`RepSubfunctor.topLift` lifts ambient vectors canonically to a supplied full
actual subfunctor. `quotientOfTop` composes that natural lift with its actual
quotient projection. The named surjectivity and range-kernel lemmas follow
from representatives and the quotient-zero membership criterion. Applied to
the last two steps of `s`, this gives `lastProjection : M ⟶ s.graded (Fin.last n)`.
The penultimate inclusion is componentwise injective by the published
`inclusion_injective`; `lastProjection_surjective` and
`range_penultimate_eq_ker_lastProjection` prove the other two short-exact
conditions. Thus the recursive splice uses proved actual maps and kernels.

`refineData` constructs a `GradedRefinement`, whose fields are the concrete
flag and a natural comparison for every pair of outer and inner indices.
For length zero it retains the supplied zero-length flag, casting the sum of
an empty family to zero. For length `n+1` it first transports each earlier
`inner i.castSucc` along the inverse of `prefixGradedIso`, using the existing
`isoTransport` API. It recursively refines `initialFiltration` with these
transported flags. It then splices that flag with `inner (Fin.last n)` across
the penultimate inclusion and `lastProjection`. This produces length
`(∑ i : Fin n, m i.castSucc) + m (Fin.last n)`; `Fin.sum_univ_castSucc`
identifies this with `∑ i, m i`.

`castLength` changes a flag's length by equality; `castLengthGradedIso` gives
the corresponding grade-index cast. In the last block, the recursive
comparison composes this cast with `spliceRightGradedIso`. In every earlier
block it composes the cast, `spliceLeftGradedIso`, the recursive comparison,
and the inverse of the existing `isoTransportGradedIso`. Consequently its
target is the original supplied inner grade, including its functor maps,
rather than a substitute chosen objectwise. `refine` and `refineGradedIso`
are the two projections from this recursively constructed data.

The index `flattenIndex m i j` is `finSigmaFinEquiv ⟨i,j⟩`. Its value is the
sum of all block lengths strictly preceding `i`, plus `j.val`:

```text
(flattenIndex m i j).val
  = (∑ a : Fin i.val, m (Fin.castLE i.isLt.le a)) + j.val.
```

`refinementIndexEquiv m` is its inverse, the concrete equivalence
`Fin (∑ i, m i) ≃ (Σ i : Fin n, Fin (m i))`.
`refinementIndexEquiv_flattenIndex` proves recovery of the exact pair.
`flattenIndex_castSucc_val` preserves the flattened value in all earlier
blocks, and `flattenIndex_last_val` shifts the last block by the complete
sum of earlier lengths. These equalities are the index identifications used
by the recursive graded comparisons. `flattenPieces m p` evaluates a full
dependent family `p i j` at the pair supplied by `refinementIndexEquiv`;
`flattenPieces_flattenIndex` proves its evaluation formula.

`HasGradedPieces.refine` composes the constructed comparisons with supplied
natural inner-grade identifications. `hasOrderedFiltration_refine` chooses
witnesses to inner ordered filtration existence for a supplied actual `s`.
`HasOrderedFiltration.refine` additionally takes an outer ordered filtration
of a named family, transports the inner witnesses along its natural grade
identifications using `HasOrderedFiltration.iso`, and applies the actual
construction. Its output family is the complete `flattenPieces` family.

`isGluedFrom_refine` treats a supplied actual `s` and unordered inner
families. Each witnessing inner permutation acts on its own fiber of the
sigma index type via `Equiv.sigmaCongrRight`. Conjugating by
`refinementIndexEquiv` gives a permutation of the entire flattened index
set. `IsGluedFrom.reindex` proves invariance of unordered gluing under any
finite-index equivalence: cardinality gives equality of lengths, and the
witnessing permutation is composed with the inverse enumeration.
`IsGluedFrom.refine` also allows an unordered outer family. Its outer
permutation `e` reindexes lengths to `m ∘ e` and blocks to `q (e i)`.
`Equiv.sigmaCongrLeft e`, between their sigma index types, gives the complete
family reindexing. The proof then applies `IsGluedFrom.reindex`. Thus both
inner and outer permutations preserve every original piece.

Repeated steps, zero grades and repeated isomorphic factors are retained.
A zero outer length is allowed: the supplied flag has the same zero and full
step, so its ambient functor is necessarily zero objectwise. The construction
returns that actual empty flag. If `m i=0`, the supplied inner flag already
forces that outer graded functor to be zero; its block contributes no indices
to the sigma type. The splice and the length cast still apply when either or
both recursive block lengths vanish. No positive-length assumption or
removal of zero pieces is used. These are consequences of the actual
endpoint conditions, not extra hypotheses.

The construction has internal algebraic provenance: subtype inclusion,
module inverse images and quotients, quotient representatives, elementary
finite-index equivalences and induction on the supplied outer length.
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), §§1.10–1.11, printed p.445 (PDF p.6), motivates the natural subfunctor
and permuted-gluing conventions only. Registered source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`, was read
for these conventions. It does not claim this Lean refinement construction.

The complete project import closure is `Filtration.Splicing.Basic`,
`Filtration.QuotientTail`, `Filtration.QuotientFirstIso`,
`Filtration.IsoTransport` and `Filtration.Definitions`. The first is the
image/inverse-image splice and natural graded comparison from the preceding
unit. Its elementary four-module closure is audited in its paired Markdown.
The new direct mathematical dependencies are that splice, the natural
quotient first-isomorphism constructor, actual subtype inclusions and
quotient projections, and the existing ambient/piece isomorphism transport.
`QuotientTail` supplies actual module images and their quotient comparisons;
`QuotientFirstIso` supplies the natural quotient constructor; both ultimately
use only `Definitions` and pinned Mathlib. `IsoTransport` imports only
`Definitions`. The additional Mathlib import
`Mathlib.Algebra.BigOperators.Fin` supplies finite sums and their sigma
index equivalence. All five project Lean/Markdown pairs have been checked.
No objectwise Jordan–Hölder comparison, composition series, simple-factor
matching or finite-length result enters this construction.

The audit below addresses each unique task exclusion in the full inherited
restriction suffix. For every row, both the import closure and mathematical
dependencies avoid the named task's conclusion, proof successors and
transitive dependents. The same audit applies to the named conclusions even
when no task ID accompanies them. In particular it excludes all segment
derivative formulas (including Ze80 §§3.5, 9.6), segment head/socle existence,
segment Jacquet formulas, Ze80 4.2/9.7 product criteria, Ze80 9.3 analytic or
square-integrability inputs, classification and exhaustion, all unproved BZ77
derivative assertions, and the three Whittaker-finiteness statement families.
No derivative, tensor exactness, geometric lemma, cuspidal support or
finite-length result is used. Worker 127's pause is untouched.

| Excluded task | Import and mathematical dependency check |
| --- | --- |
| `62de5903-b616-4b5c-88eb-a066b77c5467` | Absent from the complete five-module project closure and all proof inputs. |
| `30341ae4-65f2-4a0e-9283-763db01a409e` | Absent from the complete five-module project closure and all proof inputs. |
| `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | Absent from the complete five-module project closure and all proof inputs. |
| `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Absent from the complete five-module project closure and all proof inputs. |
| `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | Absent from the complete five-module project closure and all proof inputs. |
| `8252833d-c269-41a9-824c-5879e531b23b` | Absent from the complete five-module project closure and all proof inputs. |
| `52e97845-36bb-457d-b76f-70753334b88c` | Absent from the complete five-module project closure and all proof inputs. |
| `1cb45da2-7007-4351-a694-594fb148b8d1` | Absent from the complete five-module project closure and all proof inputs. |
| `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | Absent from the complete five-module project closure and all proof inputs. |
| `bf433f0a-921a-428c-b0c0-6475438125ac` | Absent from the complete five-module project closure and all proof inputs. |
| `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` | Absent from the complete five-module project closure and all proof inputs. |
| `23e98d90-6055-4e35-91a9-b0f5d8a84961` | Absent from the complete five-module project closure and all proof inputs. |
| `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9` | Absent from the complete five-module project closure and all proof inputs. |
| `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | Absent from the complete five-module project closure and all proof inputs. |
| `7ff2a1e9-89dc-439e-a861-a567b3db92bf` | Absent from the complete five-module project closure and all proof inputs. |
| `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Absent from the complete five-module project closure and all proof inputs. |
| `e3634665-571b-4852-9f4c-bab8a1053434` | Absent from the complete five-module project closure and all proof inputs. |
| `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | Absent from the complete five-module project closure and all proof inputs. |
| `426911b4-6620-413f-8065-04b25287f3bd` | Absent from the complete five-module project closure and all proof inputs. |
| `66e3b87c-647e-41e4-af18-df4d436765f0` | Absent from the complete five-module project closure and all proof inputs. |
| `c84cd52c-3ff3-4024-be50-8b84dd480888` | Absent from the complete five-module project closure and all proof inputs. |
| `6780b79c-9526-46aa-b8b4-00377d68b1ea` | Absent from the complete five-module project closure and all proof inputs. |
| `23189526-80b0-4828-a6d4-7ebec2cbeef5` | Absent from the complete five-module project closure and all proof inputs. |
| `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Absent from the complete five-module project closure and all proof inputs. |
| `aca8805b-054f-4d56-8045-12db7f623404` | Absent from the complete five-module project closure and all proof inputs. |
| `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | Absent from the complete five-module project closure and all proof inputs. |
| `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Absent from the complete five-module project closure and all proof inputs. |
| `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` | Absent from the complete five-module project closure and all proof inputs. |
| `ab61f565-1427-4746-ba77-46097563e962` | Absent from the complete five-module project closure and all proof inputs. |
| `67279e36-f3c2-42e3-9302-11729784042e` | Absent from the complete five-module project closure and all proof inputs. |
| `4ca79bbd-589e-476b-9f65-661e799984b5` | Absent from the complete five-module project closure and all proof inputs. |
| `ed48ae06-964c-4c84-9e62-978f5a953ca7` | Absent from the complete five-module project closure and all proof inputs. |
| `55ad1e10-62d8-46b7-a081-909ef0056426` | Absent from the complete five-module project closure and all proof inputs. |
| `b95105c6-f8bb-4641-ae53-2f49d1e7f034` | Absent from the complete five-module project closure and all proof inputs. |
| `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | Absent from the complete five-module project closure and all proof inputs. |
| `5ab445dc-d2b4-4072-80d1-6370870a4a26` | Absent from the complete five-module project closure and all proof inputs. |
| `3ff5c8fb-397c-4345-bcb3-5d98a0993d18` | Absent from the complete five-module project closure and all proof inputs. |
| `5428fe2c-013c-482d-aa6e-7df43e7191aa` | Absent from the complete five-module project closure and all proof inputs. |

The inherited names without an exclusive ID include
`Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`,
`TwoSupercuspidalProductStructure`, `SegmentSpecialEssentialSquareIntegrability`,
`SegmentHeadProductIrreducibility`, `GenericSegmentProductUniqueness`,
`SquareIntegrableLanglandsClassification`,
`Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement`, and
`LeviCuspidalCoinvariantFinitenessStatement`. They and every other named
conclusion in the task are absent from the same complete elementary closure.
The finite-length route of task `5428fe2c-013c-482d-aa6e-7df43e7191aa` is not
used, with or without a pending repair. No proposition definition, draft,
citation or pending proof is treated as a proved input.
