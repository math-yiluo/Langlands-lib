# Splicing natural representation filtrations

This is the first construction module of the splicing and refinement
construction. The public entry module `Filtration.Splicing` adds refinement of
the actual graded functors. This
module constructs splicing and its natural quotient comparisons without assuming
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

The audit below addresses each excluded conclusion. For every row, both the
import closure and mathematical dependencies avoid the named conclusion, the
modules that prove it and transitive dependents. In particular it excludes all segment
derivative formulas (including Ze80 §§3.5, 9.6), segment head/socle existence,
segment Jacquet formulas, Ze80 4.2/9.7 product criteria, Ze80 9.3 analytic or
square-integrability inputs, classification and exhaustion, all unproved BZ77
derivative assertions, and the three Whittaker-finiteness statement families.
No derivative, tensor exactness, geometric lemma, cuspidal support or
finite-length result is used.

| Excluded conclusion | Import and mathematical dependency check |
| --- | --- |
| `SupercuspidalCoinvariantFinitenessStatement` and the all-character single-block conclusion | Absent from the complete four-module project closure and all proof inputs. |
| `GenericSegmentProductUniqueness` | Absent from the complete four-module project closure and all proof inputs. |
| Multisegment exhaustion (`MultisegmentHeadExhaustion`) | Absent from the complete four-module project closure and all proof inputs. |
| Ordered strong-head existence (`OrderedMultisegmentHeadExistence`) | Absent from the complete four-module project closure and all proof inputs. |
| Quotient coverage (`OrderedMultisegmentQuotientExhaustion`) | Absent from the complete four-module project closure and all proof inputs. |
| Ordered conversion | Absent from the complete four-module project closure and all proof inputs. |
| Tempered uniqueness | Absent from the complete four-module project closure and all proof inputs. |
| `SquareIntegrableLanglandsClassification` | Absent from the complete four-module project closure and all proof inputs. |
| Square-integrable exhaustion | Absent from the complete four-module project closure and all proof inputs. |
| Regular exhaustion | Absent from the complete four-module project closure and all proof inputs. |
| `SupercuspidalDerivatives` | Absent from the complete four-module project closure and all proof inputs. |
| `UnlinkedSegmentSocleProductIrreducible` | Absent from the complete four-module project closure and all proof inputs. |
| `LinkedSegmentSocleReverseProductStructure` | Absent from the complete four-module project closure and all proof inputs. |
| `LinkedSegmentSoclePairReducible` | Absent from the complete four-module project closure and all proof inputs. |
| `JuxtaposedSegmentSocleReverseProductStructure` and `LinkedSegmentSocleReverseProductQuotientHom` | Absent from the complete four-module project closure and all proof inputs. |
| `SegmentSocleProductIrreducibility` | Absent from the complete four-module project closure and all proof inputs. |
| `AdjacentUnlinkedSegmentSocleSwap` | Absent from the complete four-module project closure and all proof inputs. |
| `TwoSegmentSocleCommutation` | Absent from the complete four-module project closure and all proof inputs. |
| `LinkedSegmentSocleGluing` | Absent from the complete four-module project closure and all proof inputs. |
| `OrderedMultisegmentSocleExistence` | Absent from the complete four-module project closure and all proof inputs. |
| Socle exhaustion (`MultisegmentSocleExhaustion`) | Absent from the complete four-module project closure and all proof inputs. |
| Analytic segment classification (`SegmentEssentialSquareIntegrableClassification`) | Absent from the complete four-module project closure and all proof inputs. |
| `SegmentSpecialEssentialSquareIntegrability` | Absent from the complete four-module project closure and all proof inputs. |
| `SegmentHeadProductIrreducibility` | Absent from the complete four-module project closure and all proof inputs. |
| `TwoSupercuspidalNonadjacentProductIrreducible` | Absent from the complete four-module project closure and all proof inputs. |
| `TwoSupercuspidalProductStructure` | Absent from the complete four-module project closure and all proof inputs. |
| Individual special-head/reverse-socle existence | Absent from the complete four-module project closure and all proof inputs. |
| Segment-socle/reverse-head existence | Absent from the complete four-module project closure and all proof inputs. |
| `SegmentFullJacquetFormula` | Absent from the complete four-module project closure and all proof inputs. |
| `SegmentHeadJacquetFormula` | Absent from the complete four-module project closure and all proof inputs. |
| `SegmentSocleJacquetFormula` | Absent from the complete four-module project closure and all proof inputs. |
| `SegmentSpecialJacquetExponentNormFormula` | Absent from the complete four-module project closure and all proof inputs. |
| `IrreducibleCoinvariantFinitenessStatement` | Absent from the complete four-module project closure and all proof inputs. |
| `LeviCuspidalCoinvariantFinitenessStatement` | Absent from the complete four-module project closure and all proof inputs. |
| Mirabolic finite-length route (`MirabolicFiniteLength`) | Absent from the complete four-module project closure and all proof inputs. |

The excluded declaration names include
`Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`,
`TwoSupercuspidalProductStructure`, `SegmentSpecialEssentialSquareIntegrability`,
`SegmentHeadProductIrreducibility`, `GenericSegmentProductUniqueness`,
`SquareIntegrableLanglandsClassification`,
`Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement`, and
`LeviCuspidalCoinvariantFinitenessStatement`. They and every other excluded
conclusion are absent from the same complete elementary closure.
The mirabolic finite-length route is not used. No proposition definition,
citation or unfinished proof is treated as a proved input.
