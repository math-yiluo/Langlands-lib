# Splicing natural representation filtrations

This is the first construction unit of task
`7259c98c-1565-475d-88da-f928adf1f613`, by Worker 187. The public entry module
`Filtration.Splicing` will add refinement of the actual graded functors. This
unit constructs splicing and its natural quotient comparisons without assuming
any filtration existence theorem.

Let `L,M,Q : C ⥤ Rep R G`, with natural maps `ι : L ⟶ M`, `π : M ⟶ Q`.
The coefficient ring is commutative and the acting object is a monoid. The
ring, monoid, representation carrier, source objects and source morphisms have
independent universes. The API therefore specializes to carrier universe
`max uF uV` without an equality or saturation assumption.

Given actual filtrations `sL` of length `n` and `sQ` of length `m`,
`RepFunctorFiltration.spliceStep` uses the image under `ι` of lower step `k`
for `k ≤ n`, and the inverse image under `π` of quotient step `k-n` for
`k > n`. `splice_junction` identifies the image of the full lower functor
with the inverse image of the zero quotient step, using exactly the supplied
componentwise equality `range ι = ker π`. The filtration `splice` contains
these actual subfunctors. Images and inverse images preserve the two chains;
across the junction every image belongs to the kernel and hence every inverse
image. The image of zero is zero. The inverse image of the full quotient is
full; the junction equality covers the case `m=0` as well. Thus the construction
of the flag itself needs only the range-kernel equality.

`RepSubfunctor.inverseImage` constructs invariant inverse-image submodules.
The intertwining equation gives invariance and the naturality equation gives
preservation under every source morphism. `inverseImageHom` restricts the
original map onto the target subfunctor. Ambient componentwise surjectivity
makes these restricted maps surjective. `inverseImageQuotientIso` composes the
restriction on the upper step with its quotient projection. Its kernel is
exactly the inverse image of the lower step; representatives give
surjectivity. The published natural quotient first-isomorphism constructor
then gives a natural isomorphism of the actual quotient functors.
`injectiveImageQuotientIso` reuses the published image quotient comparison:
componentwise injectivity makes its kernel condition automatic. Its direction
is from the quotient of images to the original quotient.

`spliceLeftStep n m i` has value `i.val`, and
`spliceRightStep n m j` has value `n+j.val`; these maps include both endpoints
of their blocks. `spliceStep_left` and `spliceStep_right` identify the actual
steps, including their shared junction. On grades, `spliceLeft` has value
`i.val` and `spliceRight` has value `n+j.val`. `spliceIndexEquiv` is the inverse
of `finSumFinEquiv`, an explicit equivalence
`Fin (n+m) ≃ Fin n ⊕ Fin m`. Its two evaluation lemmas identify these block
indices exactly.

`spliceLeftGradedIso` applies the injective image comparison to each pair of
consecutive lower steps. `spliceRightGradedIso` applies the surjective inverse
image comparison to each pair of quotient steps. Both are natural
isomorphisms of the existing actual quotient functors. They assume precisely
componentwise injectivity of `ι`, componentwise surjectivity of `π`, and the
range-kernel equality. No ambient exactness assertion is inferred from a
consumer theorem. `spliceGradedIso` combines these maps over every grade.

`concatPieces p q` is `Sum.elim p q` after `spliceIndexEquiv`. It retains the
entire two families and their order. `HasGradedPieces.splice` composes the
constructed natural comparisons with the supplied identifications;
`HasOrderedFiltration.splice` applies this to witnessing filtrations.
`IsGluedFrom.splice` conjugates the sum of the two witnessing permutations by
the explicit index equivalence. It therefore produces gluing from the full
concatenated original families. Repeated steps, isomorphic repeated factors,
zero grades and zero block lengths are retained; no nonzero, simplicity,
finite-length, finite-dimensionality or smoothness hypothesis is present.
When `n=0`, its supplied filtration already forces `L` to be zero, and the
same junction argument applies. When both lengths are zero it forces `M` to
be zero under exactness.

Provenance is internal module algebra. Bernstein–Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), §§1.10–1.11, printed
p.445 (PDF p.6), motivates the natural subfunctor and permuted-gluing
conventions only. Those paragraphs do not supply this Lean splice or a
refinement theorem. Registered source `bernstein-zelevinsky-1977-induced-i`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
was read for these conventions. The constructions and proofs here use only
the elementary published APIs below and pinned Mathlib.

The complete project import closure is `Filtration.QuotientTail`,
`Filtration.QuotientFirstIso`, `Filtration.IsoTransport`, and
`Filtration.Definitions`. Direct mathematical dependencies are the actual
image subfunctor and image quotient comparison in `QuotientTail`, and natural
quotient first isomorphism in `QuotientFirstIso`. Their transitive project
dependency is `Definitions`, which constructs restricted representations and
actual quotients from Mathlib. `IsoTransport` supplies natural filtration
transport for the subsequent refinement and imports only `Definitions`.
The finite-sum index equivalence is from Mathlib. All four project pairs
were read; none imports or uses any excluded representation-theoretic result.

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
| `62de5903-b616-4b5c-88eb-a066b77c5467` | Absent from the complete four-module project closure and all proof inputs. |
| `30341ae4-65f2-4a0e-9283-763db01a409e` | Absent from the complete four-module project closure and all proof inputs. |
| `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | Absent from the complete four-module project closure and all proof inputs. |
| `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Absent from the complete four-module project closure and all proof inputs. |
| `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | Absent from the complete four-module project closure and all proof inputs. |
| `8252833d-c269-41a9-824c-5879e531b23b` | Absent from the complete four-module project closure and all proof inputs. |
| `52e97845-36bb-457d-b76f-70753334b88c` | Absent from the complete four-module project closure and all proof inputs. |
| `1cb45da2-7007-4351-a694-594fb148b8d1` | Absent from the complete four-module project closure and all proof inputs. |
| `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | Absent from the complete four-module project closure and all proof inputs. |
| `bf433f0a-921a-428c-b0c0-6475438125ac` | Absent from the complete four-module project closure and all proof inputs. |
| `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` | Absent from the complete four-module project closure and all proof inputs. |
| `23e98d90-6055-4e35-91a9-b0f5d8a84961` | Absent from the complete four-module project closure and all proof inputs. |
| `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9` | Absent from the complete four-module project closure and all proof inputs. |
| `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | Absent from the complete four-module project closure and all proof inputs. |
| `7ff2a1e9-89dc-439e-a861-a567b3db92bf` | Absent from the complete four-module project closure and all proof inputs. |
| `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Absent from the complete four-module project closure and all proof inputs. |
| `e3634665-571b-4852-9f4c-bab8a1053434` | Absent from the complete four-module project closure and all proof inputs. |
| `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | Absent from the complete four-module project closure and all proof inputs. |
| `426911b4-6620-413f-8065-04b25287f3bd` | Absent from the complete four-module project closure and all proof inputs. |
| `66e3b87c-647e-41e4-af18-df4d436765f0` | Absent from the complete four-module project closure and all proof inputs. |
| `c84cd52c-3ff3-4024-be50-8b84dd480888` | Absent from the complete four-module project closure and all proof inputs. |
| `6780b79c-9526-46aa-b8b4-00377d68b1ea` | Absent from the complete four-module project closure and all proof inputs. |
| `23189526-80b0-4828-a6d4-7ebec2cbeef5` | Absent from the complete four-module project closure and all proof inputs. |
| `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Absent from the complete four-module project closure and all proof inputs. |
| `aca8805b-054f-4d56-8045-12db7f623404` | Absent from the complete four-module project closure and all proof inputs. |
| `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | Absent from the complete four-module project closure and all proof inputs. |
| `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Absent from the complete four-module project closure and all proof inputs. |
| `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` | Absent from the complete four-module project closure and all proof inputs. |
| `ab61f565-1427-4746-ba77-46097563e962` | Absent from the complete four-module project closure and all proof inputs. |
| `67279e36-f3c2-42e3-9302-11729784042e` | Absent from the complete four-module project closure and all proof inputs. |
| `4ca79bbd-589e-476b-9f65-661e799984b5` | Absent from the complete four-module project closure and all proof inputs. |
| `ed48ae06-964c-4c84-9e62-978f5a953ca7` | Absent from the complete four-module project closure and all proof inputs. |
| `55ad1e10-62d8-46b7-a081-909ef0056426` | Absent from the complete four-module project closure and all proof inputs. |
| `b95105c6-f8bb-4641-ae53-2f49d1e7f034` | Absent from the complete four-module project closure and all proof inputs. |
| `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | Absent from the complete four-module project closure and all proof inputs. |
| `5ab445dc-d2b4-4072-80d1-6370870a4a26` | Absent from the complete four-module project closure and all proof inputs. |
| `3ff5c8fb-397c-4345-bcb3-5d98a0993d18` | Absent from the complete four-module project closure and all proof inputs. |
| `5428fe2c-013c-482d-aa6e-7df43e7191aa` | Absent from the complete four-module project closure and all proof inputs. |

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
