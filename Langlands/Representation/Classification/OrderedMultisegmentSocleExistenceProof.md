# Independent unique socles of ordered segment products

Authors: Worker 700 (total-rank induction, boundary inputs and final assembly)
and Worker 864 (the actual-product, mirabolic and Artinian socle adapter).

## Exact result and conventions

`Langlands.Classification.orderedMultisegmentSocleExistence` proves exactly
`Langlands.Classification.OrderedMultisegmentSocleExistence.{uF,uV} F T`
from `MultisegmentClassificationStatement`. Its complete outer telescope is

```lean
∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
  OrderedMultisegmentSocleExistence.{uF,uV} F T
```

The universes `uF` and `uV` are independent. At each rank `n`, the input is
every supplied `d : T.SegmentProductDatum.{max uF uV,uF} n`, with
`d.IsPrecedenceOrdered` and `d.HasSegmentSocles`. The output is an actual
smooth representation in carrier universe `max uF uV` satisfying
`d.IsZelevinskySocle`. This includes irreducibility, an injective intertwiner
into the full actual product, and equality of its image with the image of
every competing irreducible embedding in that universe.

The proof preserves the supplied field, compatible topology, blocks, order
and multiplicities. Its product is `d.induced`, the published upper normalized
induction with right translation. The ordering hypothesis means that an earlier
segment does not precede a later one. Repeated segments are allowed. Rank zero,
empty data, singleton segments, and an order equal to the total rank are all
included. No additive character or analytic theorem is added to the final
hypotheses. The statement pair and its entire import closure are unchanged.

## Implemented proof

The private theorem `orderedSegmentProduct_stronglyIndecomposable` first proves
intrinsic strong indecomposability of the actual product, by strong induction
on its total general-linear rank. It temporarily fixes an actual nontrivial
unitary additive character `ψ`. The published p-adic character-existence theorem
supplies this character in the final theorem.

At rank zero, `orderedMultisegmentSocle_rankZero` makes the actual product
irreducible. Every nonzero subrepresentation is therefore top, and the
intersection of two such subrepresentations is nonzero. The final theorem also
uses the boundary result directly: the actual rank-zero product, with its
identity embedding, is its own irreducible socle. Thus this boundary does not
rely on the positive-rank finite-length theorem.

At rank `N + 1`, let `k` be the sum of the positive cuspidal ranks of the
supplied segments. Each base rank is at most its segment degree. Summing and
using `d.degree_sum` gives `k ≤ N + 1`. Positive total degree forces a nonempty
segment family; the first segment's positive rank then gives `0 < k`.

Apply `segmentSocleProductHighestDerivative` to this exact datum and order.
It gives vanishing of every higher valid derivative and an actual output datum
`d'` of rank `N + 1 - k`, supplied segment-socle blocks for `d'`, an exact list
identity, and an isomorphism from the actual order-`k` derivative to
`d'.induced`. The output list is the original list with each last position
removed and with singleton segments omitted. It retains the relative order
and all surviving occurrences.

The private `dropLastList_eq_filterMap` identifies the theorem's exact inline
truncation function with the published `Segment.dropLastList`; its proof is
reflexivity. `segmentInitialTruncationOrder`, with the independently proved
`cuspidalIntegralTwistFreeness`, preserves the supplied nonprecedence order.
The equivalence between the finite-family and list order predicates gives
`d'.IsPrecedenceOrdered`. Since `0 < k`, the new total rank is strictly smaller,
so the induction hypothesis gives strong indecomposability of `d'.induced`.

The private `stronglyIndecomposable_of_iso` transports this property through
the actual derivative isomorphism. It composes the two published
subrepresentation/submodule order isomorphisms with
`Submodule.orderIsoMapComap` for `repAsModuleEquiv` of the actual smooth
isomorphism, and applies `stronglyIndecomposable_iff_of_orderIso`.
`segmentSocleProduct_nontrivial` makes `d'.induced` nonzero, and the same actual
isomorphism makes the order-`k` derivative nonzero.

`RestrictionBridge.generalLinearDerivative_obj_eq_cast`, with identity ambient
rank casts, identifies that derivative with the actual order-`k` derivative of
the mirabolic restriction. The finite-maximum characterization `level_eq_iff`
then identifies the level with `k`: this derivative is nonzero and every higher
valid derivative is zero by the highest-product calculation. For the latter
step, `RestrictionBridge.nontrivial_generalLinearDerivative_iff` transports a
hypothetical nonzero mirabolic derivative to the general-linear derivative,
contradicting its subsingleton carrier. These arguments retain `k = N + 1` and
the rank-zero derivative target.

The actual product is nonzero by the same published nonzeroness lemma.
`precedenceOrdered_endpointSeparated` derives the directed endpoint condition
from the supplied ordering and integral-twist freeness. The published theorem
`segmentSocleProductHomogeneity` therefore gives homogeneity of the actual
mirabolic restriction. The adapter's
`generalLinear_stronglyIndecomposable_of_highestDerivative` applies the exact
published mirabolic reduction to that restriction and its actual highest
derivative. Strong indecomposability of the restricted action implies strong
indecomposability of the full action through the actual subgroup inclusion.
This completes the rank induction.

At positive rank, `segmentProduct_socle_of_stronglyIndecomposable_pos` extracts
irreducibility of every supplied block from `d.HasSegmentSocles` and applies
`irreducibleProductFiniteLength` to `d.shape` and `d.blocks`. Finite length of
the actual group-algebra module gives Artinianity. The published
`strongIndecomposabilitySocle` bridge uses Artinianity to find an atom and strong
indecomposability to identify the images of every irreducible embedding.
Adding the original order and block proofs gives the required
`d.IsZelevinskySocle π`. Thus the result supplies image uniqueness inside the
actual full product, including for arbitrary repetitions and every allowed
supplied ordering.

The separately paired [adapter](OrderedMultisegmentSocleAdapter.md) describes
each conditional bridge precisely. The rank induction above discharges all
its extra analytic premises in the final theorem.

## Original literature and provenance

The target is Zelevinsky's Theorem 6.1(a). The registered original is
A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)* (1980), literature ID
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The retained original was read at §5.4, printed p.188 / one-based PDF25;
Theorems 6.1(a), 6.2 and the beginning of §6.3, printed p.188 / PDF25;
and the remainder of §6.3, printed p.189 / PDF26. Formula pages PDF24–25
were also inspected visually. Section 4.1, printed p.184 / PDF21, fixes the
precedence convention. Section 6.5, printed p.189 / PDF26, records the
empty-product convention.

Section 5.4 relates strong indecomposability to homogeneous mirabolic
restriction and the highest derivative. Theorem 6.2 supplies the endpoint
condition for homogeneity, and its consequence immediately proves 6.1(a) by
passing to the product of end truncations and inducting on rank. The Lean
proof implements that total-rank induction explicitly, including actual
isomorphisms, rank transports, nonzeroness and the empty boundary.
The combinatorial truncation lemma and lattice transport are internal
consequences of the published definitions, not additional assertions
attributed verbatim to the source.

The general derivative background is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), literature ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The actual original was read at §§3.2–3.5, printed pp.451–452 / PDF12–13,
and §§4.6, 4.11, 4.13–4.15, printed pp.455–459 / PDF16–20.
The independently proved derivative functors retain the determinant
inverse-half normalization. Their Haar-modulus comparison is the published
`Group.GL.MirabolicModulusProof`; no normalization comparison is assumed here.
No applicable erratum was found in the retained source index and relevant
public source notes during the source audits.

## Published inputs

All mathematical imports below are used by Lean name. The identifiers record
independent acceptance and publication evidence, rather than mathematical
assumptions. Original exact-proof validation and integrated compilation were
checked separately for the substantive inputs.

| Published theorem or module | Proof publication checked |
| --- | --- |
| `orderedMultisegmentSocleBoundary`, including rank zero, nonzeroness and the conditional endpoint implication | `58f5a9ff-d5bb-43d8-a73d-d7e7192d973c`, Reviewer 7009; commit `31d47a6f0dabd6dff6c65e1b78f4821ddedc9bc8`; exact-proof receipt `0e38c4cc-c89a-416d-a413-aefdcf41b76f`. |
| `segmentSocleProductHighestDerivative` | `cf12542e-ed32-4ef1-b46d-48e47a342d5e`, Reviewer 9304; commit `286dd3b743f0437d22db0e793222073b9424e3eb`; exact-proof receipt `7fcef6cf-6811-47fa-b8d8-9def13c12a75`. It constructs the actual derivative/product isomorphism and higher vanishing. |
| `segmentSocleProductHomogeneity` | `30904fa3-919e-4557-b2d2-6dfc03e5abb4`, Reviewer 9587; commit `9d1720cbedcfd184cf48bf36249fc3029583cafa`; exact-proof receipt `8bd98996-c650-401b-b42f-417f84024315`. Its replacement proof has independent universes. |
| `segmentInitialTruncationOrder` | `20bbbe79-e549-416d-bf1a-e1d36b2b2979`, Reviewer 4402; commit `e40be87d4e73ac457e91929eddf904bd95d12d2f`; exact-proof receipt `22ffb488-565e-406c-9fb6-6754a27c449f`. Freeness remains an explicit premise of that input. |
| `cuspidalIntegralTwistFreeness` | `a7545313-ab91-4eaf-881e-2ad0d4c58e56`, Reviewer 2793; commit `f2f4a196a2ec57cae218f1368dade88282ce7207`; exact-proof receipt `5c315ec9-05f4-4907-9853-e87873f7dd2d`. This is a central-character/uniformizer proof. |
| `Derivative.mirabolicStrongIndecomposabilityReduction` | `18d68bc4-10a3-4b37-a079-7a4b2e3009d8`, Reviewer 6839; commit `6096ab5ac4bb214693970d29c770af26cb4cea48`; integration `6edc2ad58f754991a2a5d65a1048b08f`. This is the exact proved reduction, not the older conditional assembly. |
| `irreducibleProductFiniteLength` | `41a8585c-a5c2-4d05-a095-e31d28518609`; commit `ddf3850e87ef10e9eabe230b50f772e4890d71bd`; exact-proof receipt `4eda11e7-bf56-4f38-96f4-377c13a6c866`. It embeds the supplied product into regrouped cuspidal induction and transfers finite length through the injection. |
| `strongIndecomposabilitySocle` | `36ef633f-8d13-40cc-b44e-1452c44987d3`; commit `4e6ed28ccc687ea7e0123318bc2516e1f4b79d11`; exact-proof receipt `83d01672-ba3f-4b32-8b5d-48df432e497d`. It gives an actual atom and equality of images. |
| `HarmonicAnalysis.padicUnitaryAdditiveCharacterExists` | `72e1678f-3dcb-4058-8013-da81aa39cf3c`, Reviewer 4231; commit `caf30c941a7a27d8a483e65bbeb61b1c2f5f7675`; exact-proof receipt `ce6406e4-38fe-42e7-8197-82c3713b527e`. Its character of `ℚ_p/ℤ_p` is pulled back by trace to the supplied field realization. |

The full acceptance reports used in these audits have no unresolved
qualifications. The character proof and all five of its project modules match
its original and integrated source hashes. Twist-freeness's primary pair is
unchanged; its original 52-module closure matches both canonical machine
reports. The current 55-module closure only adds generic quotient/twist
extractions, elementary block arithmetic and compact-character facts. Those
pairs also occur unchanged in the audited homogeneity closure. No theorem of
special-head existence is used to obtain freeness.

## Independence audit

This proof is an input to socle exhaustion
`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` and analytic segment classification
`aca8805b-054f-4d56-8045-12db7f623404`. Neither conclusion, its proof successor,
nor a transitive mathematical consequence is used. The proof also excludes
special-head exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered
special-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness
`52e97845-36bb-457d-b76f-70753334b88c`,
`SquareIntegrableLanglandsClassification` /
`1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, and regular exhaustion
`bf433f0a-921a-428c-b0c0-6475438125ac`.

The consumer audit traversed every constant reachable from the complete parent
theorem through declaration types and values, including opaque theorem
bodies. At the checked sources it found 93,362 constants, 15,301 project
declarations and 1,053 project modules. The only axioms were `propext`,
`Quot.sound` and `Classical.choice`. No reachable name component was any of the
following 46 excluded conclusion families or its lower-camel theorem form:

```text
AdjacentUnlinkedSegmentSocleSwap
AdjacentUnlinkedSegmentSwap
GLRegularLanglandsExhaustionStatement
GenericSegmentProductExhaustion
GenericSegmentProductUniqueness
HighestDerivativeSupportShift
IncreasingAdjacentQuotientUpperProductIrreducibility
JuxtaposedSegmentSocleReverseProductStructure
LinkedSegmentSocleGluing
LinkedSegmentSoclePairReducible
LinkedSegmentSocleReverseProductQuotientHom
LinkedSegmentSocleReverseProductStructure
MultisegmentClassificationTheorems
MultisegmentHeadClassification
MultisegmentHeadExhaustion
MultisegmentHeadExistence
MultisegmentSocleClassification
MultisegmentSocleExhaustion
MultisegmentSocleExistence
OrderedIntegralSegmentInductionSquareIntegrableCollapse
OrderedMultisegmentHeadClassification
OrderedMultisegmentHeadExistence
OrderedMultisegmentQuotientExhaustion
OrderedMultisegmentSocleClassification
OrderedSegmentSquareIntegrableConversion
PadicMultisegmentClassificationTheorems
PadicSegmentSquareIntegrabilityTheorems
SegmentCenteredSpecialSquareIntegrability
SegmentEssentialSquareIntegrableClassification
SegmentHeadProductIrreducibility
SegmentSocleProductIrreducibility
SegmentSpecialEssentialSquareIntegrability
SegmentSpecialSquareIntegrabilityCriterion
SegmentSquareIntegrabilityTheorems
SquareIntegrableLanglandsClassification
SquareIntegrableLanglandsExhaustion
SquareIntegrableLanglandsHeadExistence
SquareIntegrableLanglandsQuotientUniqueness
SquareIntegrableSegmentNonlinkage
TemperedBlockExhaustion
TemperedBlockUniqueness
TemperedLanglandsQuotientCoverage
TwoSegmentHeadCommutation
TwoSegmentSocleCommutation
UnlinkedSegmentSocleProductIrreducible
ZeroRankMultisegmentQuotientExhaustion
```

The parent's own proposition and new proof are intentionally the root of this
check; they are not treated as an excluded conclusion. Earlier lower-input
audits also excluded the parent, so the induction does not return through an
upstream input to itself. The check supplements the semantic audits of the
used proofs; name matching alone would not establish mathematical independence.

### Generic modules from excluded-task workspaces

The following modules are generic infrastructure, even where first published
inside a task whose later conclusion is excluded. This distinction was
explicitly authorized by the trusted operator responses
`2b34e4035a5b5dafad7ad84d5a8c0dd8` and
`10df3136f50c5901b1061d52c6b92e07`, read in full. The former permits the disclosed
generic modules after checking their contents and project imports; the latter
permits the published BZ77 4.7(b) closure, including the quotient form of
4.7(a), and expressly forbids the later (c) theorem. The table records the
modules, artifacts, publishing tasks and checked contents. Paths are relative
to `Langlands.Representation`, except `Combinatorics`.

| Module (relative to `Langlands.Representation`, except `Combinatorics`) | Artifact / publishing task | Actual scope |
| --- | --- | --- |
| `Classification.TrivialGroupQuotient` | `1e56ed7e-1297-4655-9b05-0b7e49883863` / `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | Quotient algebra for trivial groups, in the fixed statement chain. |
| `Classification.SegmentProductPermutation` | `0095a4c4-eb6a-411f-8c24-e46a92b21b2b` / `8252833d-c269-41a9-824c-5879e531b23b` | Permutation transport for supplied product data, in the statement chain. The final induction preserves the original order. |
| `Classification.OrderedMultisegmentHeadReduction` | `6529dc85-0346-4e15-9152-54cb47d3528f` / `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Supplied-data reduction and definitions, in the statement chain; no special-head existence theorem. |
| `Classification.SegmentSocleProductData` | `29cea4fd-c41f-4137-8e97-14ab0cdf8d71` / `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Segment-product data, in the statement chain. |
| `Classification.SingletonSegmentSocle` | `8aac8ad9-4364-4514-af9e-e52f99707dfd` / `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | The one-segment socle comparison, in the statement chain. |
| `Combinatorics.RelationInversions` | `9e971abc-0144-4575-8205-89a2ae397e63` / `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Finite list-inversion counting used by earlier independent inputs. |
| `Filtration.ObjectTransport` | `68054cb0-7541-498d-bd52-0414519d5815` / `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Pullback and inverse-image transport of supplied actual filtrations. |
| `Classification.CuspidalProductDerivativeQuotientSupport` | `bf38b454-70f8-4bf4-83b2-0def96b608a0` / `f81d9b36-2615-4fec-abc2-50ef93d880bf` | Quotient form of BZ77 4.7(a), used inside the permitted BZ77 4.7(b) proof; no later support-shift theorem. |
| `Tensor.FiniteFiltration` | `1529e866-4b41-41d6-9510-5b00eacdd1c7` / `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Generic indexed tensor/slot-filtration algebra; its independently reviewed 19-module closure has no exhaustion theorem. |
| `Filtration.SingletonIso` | `3ee88231-270b-4cee-8670-915e76b64f12` / `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Only imports `QuotientFirstIso`; its zero/full endpoint argument uses no special-head criterion. Reviewer 7943, commit `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10`, integration `2e375c7827024fd992865fca143991fd`. The bundled `TopProduct` module is not imported. |
| `Induction.EmptyProductUnit` | `273c225f-7fb3-4cf4-852c-88d7816b0bae` / `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Actual full-subgroup evaluation and empty tensor unit; no special-head conclusion. Reviewer 8857, commit `e530d1eb7e66b0d2b988684aaaa90a729bda10e2`, integration `351b5bc54d374bde88313e8e0d414501`. |
| `Classification.RegularLanglandsHeadReduction` | `1c0aecf1-f57e-400f-8a13-1cf65809f4df` (definition) | Only generic nonzeroness of actual normalized induction is used by the lower derivative chain. No head or exhaustion conclusion is used. |

In this parent, `OrderedMultisegmentHeadReduction` also supplies the elementary
rank-zero irreducibility chain used by the published boundary proof. Its
conditional head-assembly lemmas are unused. `SegmentSocleProductData` and
`SingletonSegmentSocle` supply actual datum, rank-cast and singleton comparison
constructions; they supply no socle exhaustion theorem. The parent uses no
permutation to change the supplied ordering.

`MultisegmentClassificationStatement`, artifact
`0baefc8e-7352-469a-af38-5437d0696f7c`, contains the target and other
Prop-valued statement definitions. The final theorem uses the target
definition, not any proof of the neighboring classification or exhaustion
propositions. The complete declaration traversal above excludes their use.
The later support-shift (c) proof
`61c4254f-2ae6-4ac5-8419-2f53c0d78589` is absent; the allowed BZ77 4.7(b)
input does not import it.

### Detection remains BZ77-only

The trusted response `bd71b9185aab5d6eafffb7891bd3a3ca` governs the separate
general detection and nonadjacent-consumer branch. Its prohibition on Ze80
segment derivative formulas is retained in that branch. The exact published
`mirabolicDerivativeDetection`, proof
`3ace613e-7e47-46fc-aea5-dcd84efc51ec`, uses the general BZ77 minus-vanishing
argument and iteration, with no segment or cuspidal derivative formula,
finite-length premise, homogeneity premise, two-supercuspidal product theorem,
or consumer strong-indecomposability conclusion. Its complete import and
mathematical dependency audits are recorded in
[the published detection proof](../Derivative/MirabolicDerivativeDetectionProof.md).
The exact mirabolic reduction independently uses that detection theorem and
the actual highest-layer lattice correspondence; it does not prove detection
from its own conclusion.

The independently specified Ze80 §5.4 and §6.2 consumer arguments are retained.
In particular this parent uses the independently proved single-segment Ze80
3.5 formula through `segmentSocleProductHighestDerivative` and the published
homogeneity proof. Their semantic and declaration audits identify the
single-segment Jacquet and existence inputs and show that none uses this
parent, socle exhaustion, analytic segment classification, linked-pair
commutation, or a segment-product irreducibility criterion. This use does not
move those segment formulas into the BZ77-only detection proof. Section 9.6
is not used. The distinct nonadjacent proof has its own preserved restrictions;
the generic freeness theorem in its closure is a central-character result,
not the excluded special-head existence conclusion.

The operator-paused minus-exactness and finite-length tasks have not been
reopened or duplicated. Already accepted and published lower inputs remain
the ones used; no pending task, draft or citation is substituted for a proof.
The full imported/mathematical distinction is also explained in
[the highest-product derivative proof](SegmentSocleProductHighestDerivativeProof.md)
and [the homogeneity proof](SegmentSocleProductHomogeneityProof.md).

## Compilation and complete import inventory

At Library base `538f554630aa4cd24a084e698b1768d7143ba586`, the module closure
contains 1,250 project modules: the two new pairs and 1,248 published pairs.
Every imported Lean/Markdown pair matches the public tree and every Markdown
file is nonempty. There are 316 distinct direct external import roots, fixed
by approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
The entire previously audited 1,227-module homogeneity closure is unchanged.
The 21 additional published modules are the boundary, initial-truncation,
strong-socle and exact mirabolic highest-layer/reduction inputs described above.

Development Lake check `bc94ac9e-c6a5-49c8-be43-47201242d78a` compiled the
adapter and parent with zero errors and warnings and inspected the parent with
independent `uF,uV` and only the three standard axioms. Private diagnostic
`f1b47df8-da1b-4e50-9dc7-c13cea61e308` additionally assigned the complete
unapplied theorem to the exact telescope, printed its complete type and
performed the transitive declaration check reported above. These are development
checks. The submitted exact proof still requires its own machine validation,
independent semantic acceptance and Library publication.

The table below lists all 1,248 published project dependencies, with their
checked Lean and Markdown SHA256 fingerprints. It omits only this pair and
`OrderedMultisegmentSocleAdapter`, which are submitted together. Import edges
are the unchanged imports of the named modules; traversing the parent and
adapter imports reproduces exactly this inventory. Mathematical uses and the
allowed generic modules are described above, including imports whose
propositions or other declarations are unused by the theorem.

| Published module under `Langlands` | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `Algebra.CommutingDimensionHelpers` | `85172e1d391debcd926ad30e8f16f0207608efdffeb8653cfbb25c52ab7fdefb` | `46634f7871b87c86002de7cf4bfa7382597bc848cc809cf031c5bedbaaeafec4` |
| `Algebra.CommutingDimensionNilpotent` | `3c113d8134d10ffec7dbc931dbb424ad1e080f10fd76cd10065bd874fb88df8f` | `5b451bd3c4c2842153d80113303af0daec5fe6eaf767d4775e53b6cdb888c294` |
| `Algebra.CommutingDimensionNumerics` | `7bf0fbe0c8a0d8e0b04b7b8e18a376c604aa66ce55bd20201bb7fba62637e060` | `04d49c9f9a1b5d0a2dbfece1d463e110b77dacedc1bb4be0dc14e981c502a15c` |
| `Algebra.CommutingDimensionPrimary` | `d80b64a77d59e3ef9974bd1db775546b385013ca9b62141c512db39550c6096e` | `b345fa25b48bf37f8cac08e630cf9a23077a3a8143fdacb1bd1c6a2b87852dea` |
| `Algebra.CommutingDimensionRecurrence` | `c20d1438c77eebc4217ffa5174ee2d82b91e9538f8a0fac3171fb735161b774c` | `83071ade9b02ca6562a6838c384a953b3dede0b74792808bfd7a9cc57568880e` |
| `Algebra.MultisetOfFn` | `61316bddfa18245fcecea330d96e50ec18fa05fa9047508bf190680b82c7370a` | `e1899ab28812207fec5b9224d303a6dd68fe152948bdeaad00bf451135767a93` |
| `Algebra.SandwichDimensionBoundProof` | `5c336b3ecce8d8367c95a6a0c705e7c28191debf20077b5d4f7d0bf2d6f8ce48` | `f312d840a2e8585ac14f2ff3962dcaeb3f92ee977966b5146326dad740ed2455` |
| `Algebra.SandwichDimensionBoundStatement` | `f2972665ac11f65913ab3bcc39d93636a1e2c011f0581ef123fc8783a271f463` | `2fc3a050612b355d2f6ce573e674713b27d5a9367dfcc2c6559bbf13b5c6fe52` |
| `Algebra.SeparatedMatrixRepresentations` | `5143832309a5a57025026a23baff46fe66f026f094d603f4859cfd0351fc2734` | `0b85e3f2c61ad48c82da6431e1616961a3d2f245592ade1b9d88ba5b42aed29c` |
| `Analysis.Local.CompactOpenCoverUnimodularityProof` | `b911d8971393a2ed9d155700996ae08d039a2c3ef5c7b6a8e2de38940545423a` | `89a9eec38ab113bc86917123d3086b39e66b3dbf4fd38dc08539616fc2507518` |
| `Analysis.Local.CompactOpenCoverUnimodularityStatement` | `903c1df3437ff46c9908730f0e9b10821a9497e80f87bca9407982b2e245d579` | `ad51c34b44ef1044cd81fefe0ed4d855c8cb7266bec3a06f7b2896d072816447` |
| `Analysis.Local.ModularCompactAverage` | `5df79bf1a0b0a3c8b3961504d6ed266eb6e1408d5b681133072767140290a952` | `7107a8c6842e929f1369ed1c90dc26409d781168423fa1afed6dcd09fed45660` |
| `Analysis.Local.QuotientAutomorphismProof` | `1d52f469c06c34ca6dc3680a0d0cafdd039a16f8cd695ad365cc8b660e550155` | `f044cf536d57857edb8a93779086ccd1f7ca5bf008bbbabcf7d7905214a5f9ab` |
| `Analysis.Local.QuotientAutomorphismStatement` | `9e7bbd5fef85ada3737bc404491483779eb4d57aafb16cc3913e47bdfec39a86` | `85bae4112d6ab381dd62b433f6d5e76cef188a25c65cbe82e45e7fe5a9f159de` |
| `Analysis.Local.QuotientAverageReal` | `9ff6cd1068bea66973169c3b1f46c1c02cc61d43d0d4005c87dfe9c6f2e46f34` | `ac277f525b128f10690c60e5cb8982573d34ef4ee48ce704fade1230ec4f6cd7` |
| `Analysis.Local.QuotientAveragingKernel` | `04fe541450858b7780469424356247fcabad3d86a4f91cdd81a6dac1bf571959` | `fe441d3ed5529e1325c47e9c1016a75681d407d668ae9b26c8f6edb04e4691ae` |
| `Analysis.Local.QuotientComplex` | `45265a9540ba080428e9973ffb9e0a2a8719becf466ad0fac35e96dac3592257` | `ef37d47c61ef31b991d403d90181683b28eed0c238ec672af96b867d804339c1` |
| `Analysis.Local.QuotientFunctional` | `e289bd6ed425b05306b0e676fec978e58ea77b2a23d88db694c781def84bfeb0` | `76449616f7c0ef368ff7d8246263682ba57baf8ecfb333daac2b2ad79cc8837f` |
| `Analysis.Local.QuotientMass` | `a58a82a00a04f533feac7670afa18aab34758c753d7e774e4671a9a92456c26c` | `774af02be639b128c2fcb40583192353a0cb193118a5890d055341d2a9af1766` |
| `Analysis.Local.QuotientMeasure` | `c3d540478d96fc0aa0b527e02ab720a9018b56ab23cc6b5858960578ad0f95fa` | `63c0dfaeb6b89d9c0096a6c31e18aadb0b987b496167e0ece0ca2606fce9e279` |
| `Analysis.Local.QuotientMeasureExistence` | `6ca898a541246646a22e45e20a67f91c8c3cc9e6d023da9dba703ba9b3dc10d9` | `30e9cdcf92ee437db316c5ba2576d55c56e96212661a6efdfdb95ea0e97d2d76` |
| `Analysis.Local.QuotientMeasureExistenceStatement` | `7300d7970dc8c6bcbb434e04c6aaa0b500ac50cb8e61b7b267f068442aa37a02` | `02f50f1bdc5fbcb4ec9f94f971e0f087ebe8a0d8954fd1751eb96fc37b339b13` |
| `Analysis.Local.QuotientMeasurePrerequisites` | `4f6a46109843761a613e5c2337fe5b4be8a079bc6052ed0539ed17886fef598d` | `18496303b33302c73cbcc19d0f64ffe1fef072f1887a0c117b1f4090692d84e1` |
| `Analysis.Local.QuotientPositiveLifting` | `3463394c9485887655a1cfa842575a7ef2e4b1830eb53c95349b9d44e8326830` | `a5405d53942c08b38b68d10603aee0fb330647e56d1aa9e1466ff7b0e3e89292` |
| `Analysis.Local.QuotientTopology` | `13fd321d34ee88275a5972261c4d05fdef3f829d40b59068f1824150d7fc29db` | `d59d831110d8905b492b8550251cee37a207b008d310955946e634a01468912d` |
| `Analysis.Local.QuotientTranslation` | `1c4c8a5c4b3e36815626eb0fcc2e88f274ed2cfdd2d4a7bb9affdac420142293` | `e68d1c489a09a4020987d3fbea8f97b1124b8174311894fcecfdcbece11623c5` |
| `Analysis.Local.SplitKernelQuotient` | `46985b41cfb52f958b68fc9243004d7ad89c0158d62e680f83b6627bc67e73c2` | `6f1863bd71e7c21f4786f9e70c4363a7ba703a4c59c0eb78c17a95f4012b41ef` |
| `ClassFieldTheory.Local.Completion` | `bf1f43578844bb95ae9a8e17965524400bd0dfa723cb8d565e3937343d7b3d36` | `9e0904ee58c5786307dc9fe3935b667234ad1b50e8d54caddf02d2c827a48aac` |
| `ClassFieldTheory.Local.FiniteArtin` | `19ce709f30ef1a798efc693350f09046128cf488234ed07e795e144bac1d6bfb` | `208365b786d6fa9c7958bd6a2baa5c1d2de3a75d6ededcc246b294d4d74b8e4a` |
| `ClassFieldTheory.Local.Galois` | `c0b4086267f4070f4f04d9d8fea1f90f6dbf1fba7b5f9f833a6d04783340c4a6` | `2c98385b0434e81ee302f6f18569fe4144ab846949e4a483c0b82f783297fb63` |
| `ClassFieldTheory.Local.Norms` | `696b8c578a372037c4729160b4be63fac3365e96360abf5b50b8b546fe994d87` | `36ebee619ae3ad6ab5bed3286549564dd9ab3bf3cd1c852006bfdbad5141dab9` |
| `ClassFieldTheory.Local.ProfiniteReciprocityStatement` | `fb9b0865614133c3f860b6f42c8bf9de3319af758d7629549a3c22eaf05f6a84` | `e051e3b819b527494a1722f367b0a98d353d072154a4804e8e6d286883ab3c7d` |
| `ClassFieldTheory.Local.ReciprocityRelations` | `fcd99ef64f5ce350be95d49fbc884bc1641c7cde1f861dfbe7c030b47591526a` | `3f79e264a6e890997273c53151bd86b6d893156df4ab64d0f78c3b162312b72c` |
| `ClassFieldTheory.Local.Transfer` | `db5dd724e72eabba9420614ecfebdc880ad84af63818b34cce9c9a693eab7a80` | `c4132e8ce53521c5bde3bf7d93fd022a52248e44d31b26a56b0cf9a541b85bfd` |
| `ClassFieldTheory.Local.Units` | `4c0a4ea98a2acee28712326b598dff39bcb1300de0d77cd94aa8f90b8a6499a9` | `b68e2c249a44251f0d59505c59086e9642a095b48bdce9ed800d944dbb487c58` |
| `ClassFieldTheory.Local.WeilAbelianization` | `621fd96f76fc167e6f6b1c8cdae42d5f659ab5865a254faa36791ce529461856` | `660f1da7984574233618313e5f8e321c6ea56c2d11cfdf7c0a79e55e9ec70950` |
| `ClassFieldTheory.Local.WeilReciprocityStatement` | `b8e6143debd6db966242ce15560f28f1d386bf6c3e322b5753a2ff9b8e9a57c5` | `30f10173b6c45f3b08e52359ab1005c469d023bf10eeae3fa9383e5d34ef3748` |
| `Combinatorics.RelationInversions` | `efb59b09c44ba504c487fb32f9afe9ad7e1386bb1e6e18267d4b20385c55f366` | `68da64421f34f52594d60e01fc249823fb0e031f0b4a6499d98ac8ecac568cc4` |
| `Correspondence.AutomorphicRelations` | `09f8df847f8f2601d3694e99069051b023b6f5cc89cd23a37fc6cdedd0297258` | `5875bcd1d811af980986ef4225af1fd167a2c89848dde1874bcbf75ea90ffda0` |
| `Correspondence.Domains` | `34903bc088631a1337cb5e33c5cd73e097ee83bafab2a653419c97af8b3fe2f1` | `92d944647716a92e01c3cbb997d6bba256ef3f29a5b29fa8c99f4bbb0a24dfdb` |
| `Correspondence.LocalConventions` | `da20981c4fcab710381fc67fb9c97dd584953bf3c06a8fa33076206420746ffb` | `75f8a42bf42b6cdd714da09ff0f301ab43b6157b54016100fdb31ac64a2bdc15` |
| `Correspondence.OperationCompatibility` | `6d2b6cb9b1eed98b540da3960fd269f7cc0f74e7d222dabbe303dfb2982f0e15` | `f7cfcd49e6d0eb32629fd5d409cacb78cd796a7b88551a3e0da7b809be25ea72` |
| `Correspondence.SupercuspidalRelations` | `701f46d9e7006ef8e2868501a82b8b43a10804c8b620ce10d205dc530c7b649f` | `b68f655249d77bd7a42ad36fb3d363d7cb78bfc81b0c30f317de6a84c32efed3` |
| `Correspondence.UnramifiedNormalization` | `0e9c50c34985391524280dea47eb24e19d46660e3999262a89e6007827fa89bd` | `f8edd76283052d2b17c25e9526965c33d3b588afa6f6e80f5ec0b7dcc5379965` |
| `Galois.FiniteField.Comparison` | `0013ed178d371bfe02071000de4850d74c6782d129f8588a4df0f38cb37e60c7` | `76df9ecfea547e77581115d25862d7d2b96bd5076b5871ec9850ce3488657dd4` |
| `Galois.FiniteField.ComparisonProof` | `7f7e6495d54aed291a8ab3f802ef3bcc0fe5a2fc68a15c29fdb6bfb52ea34732` | `08f9b022b44a79bb1e89e864ba61c14f0838b42517619400a29fe6e3e31a252a` |
| `Galois.FiniteField.Frobenius` | `76728cc4d394e457a88eab5138c9bec36e900edc7c52078691fee0820b887891` | `305a7539162abe82d7a2f3cd82cd28360ecdb2f104d9462c5dde0e13d5382241` |
| `Galois.Local.AbsoluteDefinitions` | `6abe3d956b83ed48d70cd27e76272a19e41f71a9baf1fab3a7673bace9a5a663` | `ee2f8915dd7abd73f166c17341a7533e851935d19a7792073f55f1fe1520c625` |
| `Galois.Local.AbsoluteProof` | `f8460f1d2c2501ad033359dbac25ff5b62e2ea1de18fc1b72fc766c2f351158e` | `c9a96f72a7eb0e679aff37f94722aa8befec77cac24cbba2b39887c7fa57324c` |
| `Galois.Local.AbsoluteStatement` | `f1efa783a68638094de24ab78de658cf0949401e7e3154082a770bd88e6a04b8` | `16a6d3e6c5561230868ba5f0cf8005181b22ac279b6f3d7dca9c6365f0a6a8d6` |
| `Galois.Local.SpectralDefinitions` | `7b05ea4f6904f852d6870c3c323a42939d98c8e03bfc08fb7aa37a58d46e8d9a` | `ff8291f7b724341fb7e2c9fd358cea67aeed1fc9710bbefcdc17aa69fa0f997f` |
| `Galois.Local.SpectralProof` | `0ec2c48c4e49e166a62db849a3f5a2f5b65dac72a9f23e28984d2a3a880e3c14` | `83c84aba9a92719ca84dd08db3a427b7cdc63ef3f18e32987fc4513cd0f2c3b3` |
| `Galois.Local.SpectralStatement` | `f7e2504aa32d31f58435b419a40c4cb4fae7f7da332768b2439832978e769e0a` | `3ee464a49247f774612cdd289b39e14b07fba54190b84221ac1c3ef2f47e2ef9` |
| `Group.GL.AdjacentMergeShape` | `79844303df725df551a38b35ab76b18507a0a78ee207a7d92e4ed325897b78ee` | `450d0016f80800480394b1bcdfde451dac772b3b323f58646ac11ad74705a215` |
| `Group.GL.Basic` | `d7867286deba424f8f285ea9712b328b762954307fb31c69d4235c8a7b1f29e1` | `b4831fd91123aea6efd64c1da3dbddc32f0c71c9b3f31c7eaed176e7dc9a3d32` |
| `Group.GL.BlockContractionProof` | `5687c8a41c88b943eb4e37ec009adcd38bf7a13c830d23796769a1e01d0c86d6` | `c19782fd4a4f11a10a359c4ca09b9fb361f6fc247a42fa9bec96e7f9aa6bacaa` |
| `Group.GL.BlockContractionStatement` | `d16acf9fd4d0421a4b8eb24c28c63d6940c0b8d4ac1b5a8a36555e8c2470d872` | `02cb0897e3fcf84ad06be727482f9259e765d07a54f0eda770b3d29e1755fd11` |
| `Group.GL.BlockDeterminant` | `6d760c46be0239c8a85347fb324a9b0ca16350898393e7c825caa3e7f2aaa18a` | `a1973a6d66771e34f051b086b0daf2b7b0ef9c5ddb59e277154feb7d44411bef` |
| `Group.GL.BlockIwahoriBasis` | `39785ee9971758327cf715f99126dfe80152e6b43ae9d11375bfec730ce233ad` | `71829455f44c4c43d19a001232125ded644c3cc2be903b4ba574520b39e03001` |
| `Group.GL.BlockIwahoriBasisStatement` | `1da96684943196c950cdb39bbb8859ef53dc84bfc50d0e621d373298fe6426b9` | `2a6a8a54c5ab8c6ddf8f1dad3d10a102ecaa0176f909a686ceae82c869b99387` |
| `Group.GL.BlockIwahoriDefinitions` | `9693580aff0ff227d0cd1045210f6c3deaf90ff698659a740fa49aa6e5e9972d` | `3927626b38db24021d48891cc115666f35df996f03eaad466fe3d41a76abd99c` |
| `Group.GL.BlockModulus` | `20ae4dc3d7e74b524c16e81d06329f3f006941ec14f94ed9670d537f0ffb1c24` | `71d91378a443bbfa154409e51c1c9862005107510be01b40ccedd2fae17beab1` |
| `Group.GL.BlockModulusHaarProof` | `5daca39a93292b96f2bf5f1ca3c4f8b3287175e471358478f7d8c8d5b41ff1f2` | `cc9443d85bd96b15d2af6e6a3762c39a3a7cf1da29fa962be09c371069740f9f` |
| `Group.GL.BlockModulusHaarStatement` | `6ef1ac81e9cc20a61f8896953f751b1a492008256b6540348450a9452c53562c` | `33b1d4abcb5ea1524e85a6d88899acc081ae3c811b0e8e382b47a0135b03ac21` |
| `Group.GL.BlockScalarCenter` | `44de1dfe1c2e5de3b3f127e1cc7747dc699f66c106fe509ea1c83b006b425197` | `f8425f6d9e6e94b63332f3a2ccffd2a0ac089f444d069c407bb2198c43e24bee` |
| `Group.GL.BlockUnipotent` | `13165f0e60076a5a62d114909f65c9e5a9a7e3060cb88101cdae26db21077d4c` | `961492ac42a5e7c3c712424a0d11b9b2c3d280ccd262bc799a601c149a8369f2` |
| `Group.GL.BlockUnipotentCoordinates` | `12c1ed669639e799e7c42bc8006e2ef6d6747802d200299329334914d913e1b0` | `b498dcc3bb5130c907ea1dcd6a490e13f871c14933fcdaac4b3bf4305c8f68bb` |
| `Group.GL.BlockUnipotentHaarProof` | `ade3b6483f62acbbe13dff46feb3a2c4556684f7cb2aff243854a200b8070c73` | `e259545e632933a823ff659aa7f43ad65b9ce77a462661dbfb4d2a177dbe7e53` |
| `Group.GL.BlockUnipotentHaarStatement` | `8b1dfe7dcaf22760546ef1c12255541643068b033a499d433c85043c3d8b27bf` | `b6c99f2cf13b1caacca98f9de949bbba83faffcf7b13ae3c2f1bec0c62d76f0c` |
| `Group.GL.Blocks` | `577cd4a9940a803f12b9bbc7edf8864c791271f13189d70eef5ee81063ce5e06` | `7c9ee8c2a57329f5518134d1bb9a99f4afb868f49e8f0ac4a51b20ae3cc110a8` |
| `Group.GL.CartanProof` | `958ea5d1ec045304c5c6e77a7eb299e828ad8ab943647736096dbdaa9cab7ba0` | `26c8197863b7e1bac1c1b5a5211c14618cde0064f7a5c91421b683a908788dbb` |
| `Group.GL.CartanStatement` | `123d73461be89dad739e660d3e2305388b786043cd69dd903dcf55623afe0123` | `54ed9896d392a4374147b782dff4b2fb4ed088009c3e722211556d08767053aa` |
| `Group.GL.CentralQuotientTopologyProof` | `edc60e575b21ebdcb1c22adad4c642f2d0ce25236c3c3f27c4c856979beac81d` | `ed3879aef51e77f61727ae7c88e38c31b358fc4e2379d785d4523143dfc2c8b1` |
| `Group.GL.CentralQuotientTopologyStatement` | `2e439916cf77df56962e66a8bcb0d0726ec2151aabac89cc83007d06386353dc` | `d464f84c02e9505f960a8697ef2c5706d77b1c02b25d6f479c18783ae6a6a9ca` |
| `Group.GL.CompactOpen` | `4fb0ec8157733c5dbb582932859cdcdf6f26513b1adc9e5e6b0cd895eb147565` | `2af058527bc82f616fdface9a7ed0ea576aa2fcc00616c0520816cda79e6797e` |
| `Group.GL.CountabilityProof` | `0a01fef68b555396f144f26e9f47694a9505f92fffb3c1b9362fd4958d26bfc2` | `8f8548907f8493627102277f9494da267ccdb85016fb94614753c00ad4fa9235` |
| `Group.GL.CountabilityStatement` | `e64f82c4b3c87bc0e7b1d7f05471241a314ea3d33cb1fce8d26f4da40ae57ade` | `0bfbf6b6e971814cab627b23a4518ae0aea504c7aae140c3ad1ce6f350ee472b` |
| `Group.GL.DominantExponentGeneration` | `b1eb4db99a01c2dae1b80f58b0fdf2c9dbc727ed82711c8917c5725d2f4e6046` | `1864726c80b19cbc7ea9d9555db823f9086ae1924e53fb3c9ca2e5f36c6df60e` |
| `Group.GL.HeadTailBlocks` | `0b72ca182692cd8f33c101c3099ca44dc7d6527630ada40857351a315090a9cc` | `69fc0af89b28e646a81a65400324382f0adcd12cd4432178de889853dadade40` |
| `Group.GL.IntegralSubgroup` | `c33d742fbb65dd3451ab4d54b4572135763eab50d52d6e327895e3ee80d6547d` | `5f5bd25cc6606997c1d330b99b0292618895c5cc9b7dbba9e6a7fa2c1c6d08fa` |
| `Group.GL.InverseTransposeIwahoriProof` | `8debaf768221518e0e31e26eee0e0aff640819d56dc18836edcd11c1ae04b8c5` | `d9121520db18ab46c753ea7d6cc79aa8b80687f16b6ccc3f5b60f9674b486b0f` |
| `Group.GL.InverseTransposeIwahoriStatement` | `fdc3add8ed593454265071ce065176eb1aa6e430da715d61eade4cc206bdac6c` | `611a702f801287a6cb48099d0ae13be8b6340cc8da9e8742271c51ea096c33ef` |
| `Group.GL.Maps` | `533caa58120ebdf7bf622cc98888b1562dad950e5e731719d9b612752bc6bb83` | `529acb945ec0bb824e3c2d9fe2c54b2cf01df353966495896d7b93c96c627a2f` |
| `Group.GL.Mirabolic` | `358505b5bb7db8a3c7d1ae8175bddb476a7cba621a8407f4180fc1834160a7a9` | `b7549d1b35fa084279ceafc6dedb466a4914fd9b21434b0cd6a0e3afc03e0399` |
| `Group.GL.MirabolicMixedOrbitCoverageProof` | `a67e03b239b184eb543b951c2abcab71c1459462e05215683361b036c8201bb6` | `4beeada1c54bcc2c592094dfd112f9909074c71fa0f7ed0b094c28d4f3c97688` |
| `Group.GL.MirabolicMixedOrbitCoverageStatement` | `da09561cad6b79f315a56aa235cc94ea328a0f21c5d9af823e58029414686f0a` | `378510114a04fda7f6ac227d39535596fd7ed8bdab69faa46bb59a6332e04bdc` |
| `Group.GL.MirabolicMixedOrbitData` | `182be30f22602c523bbc92eb41585ac64b4a85c4dd64c27ec96eeaf8e52e64ee` | `95f33a07e6ded558f3c4a899656d57200db9d19c1a663a8d6c29e954542ef60c` |
| `Group.GL.MirabolicMixedOrbitRadicals` | `d39cfcdc285d2f5ec6de96b9802f7ce55dfbc189826b4177be1336a198493f15` | `15f9e7b831c18eca13e426582a66e9a4e66299200eea1dc553c3dfec8e1e6de6` |
| `Group.GL.MirabolicMixedOrbitSectionCoefficients` | `82749dc25a6efbf7c4588f2fefe064f0fafa9554ca11d2772f6d4c0683f6c2fd` | `4f7b21565623354b4e815fe67f20593bcc90bb009dcd2f93951dd0df32d94d21` |
| `Group.GL.MirabolicMixedOrbitSections` | `fcb9ef4ce81f9b03f5813b8c4935886b00a4d88de6d2b2f200fc121493344920` | `df5571e050755d26b68d85d1d261c02caa90db180b0e37ef934c964ed695761d` |
| `Group.GL.MirabolicMixedOrbitSpecializations` | `e4f5291f755ed022f945466662c17e7c4f6b6ace6a5e8613cb05f4db801a7e4d` | `788204ab4d4a50a3669a9d252d15c899b45adab061337e6ab5e7a41688eb91d3` |
| `Group.GL.MirabolicMixedOrbitStages` | `fd4983402336be1ebfbd48935d2ac510ed4d1e2dcdeb2bbccbb60a498781a117` | `7ab26627f379c864b53a0986ebfbec3edfaadbc9e748df95a34b46a497398973` |
| `Group.GL.MirabolicMixedProductSubgroups` | `1629a5402c8995cf576883fed41fc5590c36d1aeb547f87ce62ce39f755d5157` | `700f419ffb24a951e04763a27de166ff1d3941ec8110c4eb971f37b27ed2fda6` |
| `Group.GL.MirabolicModularCharacterProof` | `fa253a75023a1bfeb05a2a296b1904791df77bbc0e12f34f4a2cbf957e5d1bc1` | `effab920444a9abc672a2e4994abd46ee18db96a94ad94168e96397eb80da1af` |
| `Group.GL.MirabolicModularCharacterStatement` | `973de323ba362cbebac9076a841251e3355197e7e1dfe986ed51edd8da5ac716` | `5540ce44b1111ea3d5189cbdc6dcd2650dc7b9ad1d743668cbf63880a26d6bbc` |
| `Group.GL.MirabolicModulusProof` | `9f899e92c826ce169b9fe6157aa0e3d92cb114d838488f2b13fc6cf9adac259f` | `d0e9a06c2d30d4ff5b3b2c139fa92e65f645b424b9f5f3c91e108fb851007e99` |
| `Group.GL.MirabolicModulusStatement` | `524d0c7ff5073db5955a72aacf748090e42f68b3f0aa24098db8d67ca5c375bb` | `2390593e4cf2ddd8c9ee205a396cbfeb1acdc8ecc5148161e17a5dc134f790f7` |
| `Group.GL.MirabolicOppositeIntersection` | `d63c6fe33c0fbd27165fa2ffebf5a23f8a53170ef6c64379065e65e95180d0c6` | `4ed0d43b2947020cd52ddc55b6f9721cc82e526b72b4cd7c6e8f7daabc631711` |
| `Group.GL.MirabolicProjection` | `48ddcc2f501eebf37b70cfcb26be042530e50b73df1ea5c31f928ac18a48a90c` | `cd1210bd7bf8fb47239171c04d9dd24e1f934efcabdecf2339a5d57517dcb6b9` |
| `Group.GL.MirabolicRadical` | `b75812e0f24586a5b6365b6282088886d7f359fcd5bef368136946b5b6137eda` | `183e771f6e76b3094d607822e15effb869cd80bc1666c7e76962e86c27f58eed` |
| `Group.GL.NestedRefinement` | `91ba13813e1b9d130d1ed3246ac577aa162a8e2ada814b08b2df3cfb0400aec7` | `a63aed0f05537ac34defb06c900983c51b4bc6750636ca7b42cf50ddd0f2ac66` |
| `Group.GL.Nonarchimedean` | `81e9aee8a06787452e827803cdc32cd1bab00b5988dfddbdf85a9762b79f46bc` | `16db461b54c5a193c29f5319bea7fa2e3d454a5766b2cd94bf8ee0a3a655b042` |
| `Group.GL.NonarchimedeanStatement` | `e6c1d5e722bb4ebf86de405f0bf4e57627c19fbe3cc7e4bdfbd5a31b6af1b63c` | `f390f56b1aa616cb1e5226df67f7893e9c33248e51d462197e7461862cfc1a10` |
| `Group.GL.NormalizedCharacter` | `31deaadcf15cf03e88fd00e26452df03cc103ca9bae18206dac748b9b6d53568` | `296f42c5aeb400f8d131210db13508fff6f220755b08b8c4b8a6f9c129640507` |
| `Group.GL.OneBlockShape` | `d1d2560f8cc95aeb9d0e0ffdb3be6b72fd6b89a3dd9241bbfada0014f9e06c82` | `36a71d2c651c0331875f98f75723192f8b11d2694e98d72e0c974ad7ff3d0f30` |
| `Group.GL.OppositeBlocks` | `60311593961a241bb6d282f110ec9f80aee19e0c40d330a1493ae5594b0c0703` | `e9df7f1c4c3c1fde7a6d2ee39d8650ab9ceed264424cffd3626286d4e4ed2d35` |
| `Group.GL.Padic` | `803a2561ddc85a54c7846a421d37ed5dc61b8974157b02b72c26bc41d96e1722` | `380b41087f6569d499e54580e487d1da0755236b84ec3085649cbc37f7a66d89` |
| `Group.GL.PadicBlocks` | `85860a6c72c15e5bbf6ea49a632bceed30ea868ef5c05f018d0b0633b35df068` | `b5b301f61830df6628534f77826bf8edac571fa7bab4b79cfa74ecf371317b2c` |
| `Group.GL.PadicOppositeBlocks` | `82097e3c2cffffcbeed167298ffa819dfc89736ef6d9cb234a25b0730eec08c1` | `05d7d0f9ff4a35c099970444e9fb6ec18666f6b480e1d8120ffef32b99acd29e` |
| `Group.GL.PadicUpperUnipotent` | `2b70e37021b6fa5ce1541cf35e929f22cdf121563f7fd9cd33c1fe109e5abb4f` | `78034e93967a2e4290070b7822b192edaa52d31edd0d6b5be66327e0f40ad4d5` |
| `Group.GL.ParabolicModularCharacter` | `1c2f3a7fa5828e1bc0f040caf7200e3002ce75e21cfde301e6b1bd06ed093912` | `02f1a1e4cacfabcd497c5dadc646e0029009555cdd33bd379ff108ba6c117df1` |
| `Group.GL.PrincipalBlockFactorizationProof` | `e731b6aa21632116476cfbdb75c59d8df383f21bea9e6aa133a081b02d0fe9d4` | `5aad90dc54600a6a66cb55c4f692c8571da6c56e6f3846b513c22ec3fd76d6d5` |
| `Group.GL.PrincipalBlockFactorizationStatement` | `e7e553564b2d422a26296d1164a794507d64c308c40c443721ac7dfeb107fefa` | `bbaa0837fac63291f06a32f0926ba010166ca473b44f0f1edaa9d1af3de60286` |
| `Group.GL.PrincipalLevelDominance` | `d360a5e0ddcffcede9f383f436a2160fdd99c4b4a5755a5a0dec58710d94c637` | `f90d983fe7f66fb1500cff4ff6f58df0902e40ff3c628b760158b0c5dedfdc0e` |
| `Group.GL.RankMaps` | `5cd299ec27e66d96bccc8bd9a67d69ecbbc42974351b143c44838f32dd03de41` | `507811ee6523775ec504dbf4ee4b9b783636fced040a6d1780e709743a393653` |
| `Group.GL.RankReindex` | `bf919939a42579c309607e08b891b2a4014ceb500c50dc482f40dbeee521b7e1` | `84fe7c62aa642f2526aff6269a437fefb07b291f5c3c125049e9db2a0ad7e294` |
| `Group.GL.RefinementCoordinates` | `aa0eae031ad656388e62ca1e545bad60d6fe30b205bf2718bda7e98d2f72480f` | `bc999de4dc0b4cb22e0ef8ba5ec1ca5cd0c9abe8617814b97192c10c9ce27bf1` |
| `Group.GL.ReindexCongr` | `d275bfbe414ecded56d2d5c37a09f37a2a2d70dfcb8546c0f4a9e0408bb71eda` | `78d09018acc494dbaa129648124a50c59ccfec835c9bb393da7ea484b43c955e` |
| `Group.GL.ReverseBlocks` | `21cb25bd7866f8508dd6872e6e84bd1c7265be35c69ddd069041f39c74994bcd` | `267e7d9f8d66078bae68a7a2c649ea1fdcaddb7c9e9a722e9712b6513c839362` |
| `Group.GL.SingleBlock` | `ea7ae10c50b01933dc1ddf42bb1b9a06d53605d8c7433db51271c151759f7dcb` | `756e5d0b8e50ed6a81a8161853ec1feb9361b3d11a22c86477312633a667e3f4` |
| `Group.GL.SingletonBlocks` | `e509b5ca9e63345f3fa5d40d6898f5d91963a962316bf685082c228b079e3c91` | `3745212e43a25747aa64331cd9c34d1f909936939b3fad58bac3f2922f123347` |
| `Group.GL.Transvection` | `b7387e9e134c6fcaade82ac179ebd1337e2d423a3d0d1199f42bcdb35dc7fc89` | `1d9de118aec46d9dce255fa1d407355c3862b2a61b3c7f485870f0f798b3849a` |
| `Group.GL.TriangularParabolic` | `e72676bbf38b65f43d68e28bad589eed571875f49affdc14bc5ab561ad0a65b9` | `97624d28ae7d04e777f265e8c55fe14b3f33e714360fef684262ad241376d222` |
| `Group.GL.UnramifiedCharacter` | `69df6a7fd220a7303ae5969b6c0a35dd838f92d8c5474b41a9aca161d2ded43e` | `5da84303e1e73bad8d5c90414db49f88ab77419fa0b7382dfbc79be69929270f` |
| `Group.GL.UpperBruhatBoundaryProof` | `01c9100450f3352d09f8f1a56bea997af2f7e4d72b7f546472b3835dc6993b99` | `56b008ec75b3175ea254cb449d12aff6e59ce6fb27c73e33f90948467ac74891` |
| `Group.GL.UpperBruhatBoundaryStatement` | `851596bea12d0f5cc7f1d91a99977f24eaa7c3f1321cc56af73f8e6aaaa032e4` | `6a56e7bd46f87f8831344c1c17fdf58766e1e6c8714e31670b0e8bcff31d9a62` |
| `Group.GL.UpperBruhatCells` | `e25c5b41436d5715967e10bc1cba9a2bf2fe968e693fe43b288715a509443b19` | `5b419d817d1fa66a362ed7af7848faf080890ab96f8cb35677943b97b3aa0b99` |
| `Group.GL.UpperBruhatCoordinatesProof` | `eb2cc9bfd8bc77973fb6b6ca9a2506622ba7356cf641b92bf483e46dd60f15b5` | `958ed945dbf38345aab9ed49111115d3146391085cab863f3f2672c7a54fc400` |
| `Group.GL.UpperBruhatCoordinatesStatement` | `f74dd2029843a5d59d4072cefc8f2d08798a461bbbea6519bfc57f60a7ea405a` | `8351a57e54b2d6da5be6b7f4a9d9fd1d99c922137f47b1d4842745308a971f09` |
| `Group.GL.UpperBruhatEmbedding` | `196b98be5f430dbdf58cbd0432062442de0a4e98a1612225c0b39bc0d7d4d647` | `c9c93c8db90e7fac362ce06766ab6c863a1c31be7bd431fc3f2b094ba0fb9d68` |
| `Group.GL.UpperBruhatFiltration` | `f1cb25ff8b33e351d1e24149c477452357cc121467db5f32e420caa6670bd81a` | `01f89c324f6524d913960263e0e34ea19c2f762d275b9ae9d376905f21862e71` |
| `Group.GL.UpperBruhatFiltrationGeometryProof` | `7c8a7887faf3f52fd9f092782972e98590e09192f60359b7db1bf4dcee05d9e8` | `fd6d136001875d6cf5bde085c57179f844c9616a4c605fe42adf1ad0296e6e3f` |
| `Group.GL.UpperBruhatFiltrationGeometryStatement` | `d74a9c24a9d39559859edd69bfc3a06708d00dae9f83fcf4db4d677fa6c7f4d3` | `cb31c1eacd73970ceba1a1d066e9635020f933c9028bbad910b606442c088839` |
| `Group.GL.UpperBruhatLocalClosednessProof` | `5daba928e3589ee1ebeee12af85572d98ce052bcd91820f56589022a16402611` | `2b7bbe8344c8a973a680e61089ebb030bff8652728c184315902f63b6d18f1f0` |
| `Group.GL.UpperBruhatLocalClosednessStatement` | `604750a387c05cf894ff07d417a9e00a397e5c0d0ab1b7894e8297e696649ffe` | `0403f8f25ae9c34008b2d35a6da612344acf6042377da1c2904452e648d4a51a` |
| `Group.GL.UpperBruhatPivotProof` | `b5a79c51f0352673919690f70ee54e7a25f55950c1ce3b3ba18b382cf4cd07ba` | `a963250c2b2631a1a597dcda62e6bba9b3ead6e7ecb8c0a2c5c1994d1b39d972` |
| `Group.GL.UpperBruhatPivotStatement` | `34c4fea1e154953328ffb51e58342efcef5423ee961b9b97a81ab04e0b07eeea` | `cec7e00e1c218941d2bbb176bf259f36ffa0de367ca441ecac84c668456cae89` |
| `Group.GL.UpperBruhatProof` | `3769a6fcdd5125ac45611d729323e0e3003e665cf541f9391055a9da4a81f746` | `6d16004d6a6fd67ef3c3478e8cbc8014060cbceb7b6c13e712d08ff36c081fd6` |
| `Group.GL.UpperBruhatRankProof` | `0ca7be63cedc3e6b9336f726547ccfe0258697568c1d4cf4ceebe50d867c43c8` | `a5118d2f11e4fb7451e6d33d3d5fa382aa8f3dde48aaf8933443e82b48679159` |
| `Group.GL.UpperBruhatRankStatement` | `dee041f674aa56a2fc1243036934d99c662d84a3367833d1b12b39b748ae7134` | `d450688bbf2fda933e74b16da2b1b969deabf8935ffc288f8887186970a3d9c6` |
| `Group.GL.UpperBruhatStatement` | `454bd0474ce736cdc130af380157aca6a09f38724ac828c78c18bc7533db1012` | `f97a9775eab1661bb157dbdf38db2f3fc309480b11e22c179a9a4a4a592cbeea` |
| `Group.GL.UpperBruhatTransposeProof` | `95de0a57a6f313c4b5573d99a51ab3ede26ab2352a9b98e2ba25deb0b685ded7` | `b91dd855123a35d1ac136002809be764460d3c2fa263497d67c41b5eadfe91f8` |
| `Group.GL.UpperBruhatTransposeStatement` | `6e162f8262f5a82ad06aa180e00ccb5f323b122939c784e822abe2d5da9af4eb` | `a2e2fc125ab532d20f8c430bd7c838caa09b8e9237b5277e9959a75e9dc277fd` |
| `Group.GL.UpperUnipotent` | `6c2858fa5f866777a0cd3066f3bba643d3300ef24bc1532a3d034001d9ec28c2` | `bbce6c75bc9a59268b36ee5d4fa0f475b59be64dfc1a396b897cf4937269c02f` |
| `Group.GL.UpperUnipotentCompactContainmentProof` | `d399f2d64b4331fe8dc8d3a7dcf3fd577dbea6cbefd0bbeba7ea95b0494fa6e0` | `ec9afb1aa92a8723b7a790366fef9fb46b655f0d60c203d3c765fd10f5562185` |
| `Group.GL.UpperUnipotentCompactContainmentStatement` | `f345f3feaae9664103579987ae70298a8da3b7a79d399b8a49bee913e09dbdf2` | `7cc86af9f4ba4042b709c57f1f4082681c66b8dfdabe904a0110ca3c6984845f` |
| `Group.GL.UpperUnipotentFactorizationProof` | `f790ea3960e15749364c7a8d39cf568b008334c1950856692dc83bdf1322e7bc` | `9238b3bf27f118417936e4464bb5ed746cc513590c192d263b3cd6268232ecd0` |
| `Group.GL.UpperUnipotentFactorizationStatement` | `31f08d562b8054578d94c35846aa1b750e49f03bd5355225139cfc45fe9cb2af` | `0bd11188f5174619b1d277533756d15774e2595227075ddcc3cde7d084841ad6` |
| `Group.HaarModulus` | `1e036132d276a4380b2f5a80e8ac69d81a4726c8f3648169e94ee7db97084f3b` | `e47c8bb2e8b2e3e639005b9a4e866d58630ea301c3776650d1418fa32246a3e8` |
| `Group.LeftQuotient` | `879867129dca8629e6f58cd8feda5665073e565732464962995dadd19e702c4b` | `243eb55c5ab128333506baf0aebc302bd95fe751f36b3c427bea020fe19ba8ad` |
| `HarmonicAnalysis.AlgebraicIntegral` | `9ad40c526eb1c8faac1856a4bccd2e267b7129091c5412767fb35b1ae160d5d6` | `485b1d98ebe2e74c96a8800af13aa949674a417a0c1d988eae6d56659c7e1011` |
| `HarmonicAnalysis.AlgebraicIntegrand` | `46114c0e0919b97c7308d5932e68c8d57fbc5a8ffbf9066b0e99d6765c75ab1c` | `fd776d62b8d21dcdead47376459e54112c0591ac705ff4269bd8752a6e7fd8c2` |
| `HarmonicAnalysis.Basic` | `2198cecae146fa7f904dc2c01169d6321aee8e155c99614ed92f861fd2d65aff` | `770a9f6e068d76d72fb10ff91ee1a27b66696ebf0c52af23464fb4d0956ffdf6` |
| `HarmonicAnalysis.CharacterTransport` | `b3d6abbb78f03f1e2957734f75e40fc9e284a72cb1855777d9fc5879a3f67b51` | `b24e9b1562a021ea079d0a554312a7e18c252bcc6c77a764caa347a94354074e` |
| `HarmonicAnalysis.Conductor` | `1780ea3172b1c84654e647efa3208d12c669a8c51a0942a1b80f4a66f84b4a53` | `ef4097816de90b81e1be2bc9b1dad6de7896a8b9fb658e122afd8876fa7faeac` |
| `HarmonicAnalysis.Distribution.Basic` | `afe9f5d3d554618f4f1a6479a9fd5083eba3ba720696c4b97c13586a40f0d4f5` | `53d9e23eb8969c384f6bbacf95a7aa50e658d0fa64ba3b2357bd2a2414798322` |
| `HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof` | `0f92f12c81d39e7d16c280e99c38e1f9f22da05cc7504c899188e58b026ec925` | `aa9b6fc3f2f43f5e453e2fe647bb78f43ad3e97f4f313fefe835d3d4ef4822f2` |
| `HarmonicAnalysis.Distribution.BruhatFiltrationVanishingStatement` | `ce35989470a45e721322114cad83c73f53876264643d3461a8117adf3ca70eb4` | `01680ac7d3da07985e1b6de8ad60929d51ed641368f9f2778941b4f401e135ba` |
| `HarmonicAnalysis.Distribution.CharacterAverage` | `37c7cac0a5183f72d3ac8857a8eb911b0617f87cfdfe006fea422944c7574bff` | `294ab5a15e2951575e0059516dc31facd6e9fe59fa848334cc0db9eef496ba83` |
| `HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof` | `687ae3d26e8158a7b18276a6ff53bcd62ee40f8f1ce2685f84a59ab3d06a0cca` | `bee2880834e99fd9aa6d21a905dca6c1833113ad2785c16ddfbe56a5b58bf8ef` |
| `HarmonicAnalysis.Distribution.CharacterAverageCovarianceStatement` | `a15d714788efdc8bc5c9b7bb67fe8dba2477c766090b5c912a6b45f90cf2caa4` | `ecedf286125c7be4b441b11f0eb6aad16e9a219ae28ae40d257c7b23f122be71` |
| `HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof` | `e1ddb384f13f9d5a346c1540455eb13ae40fe1a1bfcf1f4e6e7c521188682555` | `1e66e27b434eed4bc090f4262f620ca221465bcfb5150d7f64c5c4a1a09e66d5` |
| `HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement` | `92a8e2876d5fa295c8541bd264bc2897810c71a6b31c8746583955535939065a` | `739c0b5a0cbd8705f08e55e8a0ece0d8c450c7bf4a62edfaff7bc5035ea00c11` |
| `HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof` | `ef98e930f53da73611b7e9a06164c2730e46f44588fcd843dd67423998aba54e` | `c0e101665272707eaadef3c27a6f1cd9a0253b52ef06da4a233786aa6873a27a` |
| `HarmonicAnalysis.Distribution.CharacterAverageSurjectiveStatement` | `1f24aa5b88a72bf612addf9d252e2565177febc9929e6605e205932f460c7d6e` | `1d306310c6ce6b88f36b001c34af54e59d29cceea9ee299bb7a744b5849bea6f` |
| `HarmonicAnalysis.Distribution.ClosedRestrictionProof` | `2feb2c171ee1b9f2eeacd50640b4c17f473aefae11bd9d373f8efcc0f2c1c3a7` | `69b4c74769de51e2554fdf08cc8b3c1b632919f4bd6458d3f560845e65461d48` |
| `HarmonicAnalysis.Distribution.ClosedRestrictionStatement` | `190d93aaa176f351c54128b382e8bc9e4847d5a74c9a996bc5e7287b7c0e770d` | `e215a7e742ce54077f92d54776be810ed3b3d6dcb6696a9e4e3a1c04211ec3e4` |
| `HarmonicAnalysis.Distribution.ClosedSupportedDescentProof` | `d5bdc209899c48b26786d71dde50f4c57097934c89e78884f6635601dca3190a` | `04cdb7eb21d072b68c9e8e8d3f55f3f0ee4e29899b02bc01851d7f5cf63fc08e` |
| `HarmonicAnalysis.Distribution.ClosedSupportedDescentStatement` | `ee0ca09157003fbc96c4d9bf71d40b326703cd12ea36341c3395b61db81c7d7d` | `cd13aa1d64bb4176d702669b2ced12979eed6410e418c7098f2ae608f69fe6aa` |
| `HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof` | `0de03c3925493b8ebb537be644142c35768b77adec0101b94b0f6be2985984bb` | `2022f9509de11820f5f617c20f223858bcf9bb74b8a94d69a150b1ccd50665fd` |
| `HarmonicAnalysis.Distribution.FiniteOrbitVanishingStatement` | `86ffea02d47def7f5cc7a3507233500c9a167c378f78addabdd749c3e33ec597` | `bce062b00e0daa9153a770eba27dea9c744c4249b48b836794ca39af828a4c7a` |
| `HarmonicAnalysis.Distribution.GeneralLinear` | `f636fa12b8e1dc16c0faa09c3de090894da8a5cdf32e47164bc8514422b4bf62` | `27998b23f211ddff6ed2dccfe8edd4f2014bd0cd043431a8392e1a034f1a1c23` |
| `HarmonicAnalysis.Distribution.HomogeneousPositivityProof` | `231203a0d954d4164e97288c136791dcec6d8f455e9605d3fdf89425625443fd` | `02f5c00a88e9943ebb9713228d8c532d53752b68b48bd84c90755c7303cfc7b5` |
| `HarmonicAnalysis.Distribution.HomogeneousPositivityStatement` | `04a3803dd7b2f1c87fad9fb83f4b4053fc0724af4d935e29604ee2d29f730ed8` | `d6270237a246b7c4b9a3228fa599a7b6f9ebe77fa917c9d4efdc996144abd701` |
| `HarmonicAnalysis.Distribution.HomogeneousVanishingProof` | `4dce798f5f9d4a6126376dbb4f0460b347afb3797ffdc835d92e550b23a3189a` | `dac63d0591e12016275e6be6d616b17d33d0665cd09c6f60c4dc5c1cc1dc5e2d` |
| `HarmonicAnalysis.Distribution.HomogeneousVanishingStatement` | `d790186df289d18e8e32af8fca9033fa743c40aa9ffe1d06e30a392a5c8bbaa3` | `af6782d726a55b882c54d39b235090f0ffe5c28fdf3c9ac6e5465fe0618fae03` |
| `HarmonicAnalysis.Distribution.LocalizationProof` | `a04c3185300dae73e5855da19a4ce68df599fdce31449644256d6f83fc23c626` | `f2716cadf9075c223a0a17d5bdcd7a3e0622b28866b4cdc164eb47b4d697f085` |
| `HarmonicAnalysis.Distribution.LocalizationStatement` | `de0062663915555201e89ed2ae0a3cc65bb8ca6cf6ed241da3f7e7e5d8c5ace9` | `a998bbec6cbbf74295b0e59d5503596ec394f34496fd9d53f196341db01e3541` |
| `HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof` | `8273f4db337cec8290e43a0406953b6291b7ce08da1e4a1225e9c428a718f1a7` | `b2309f346a19cea043eb451b8396824ccbaa702ab098e79583272d197d2a6d4c` |
| `HarmonicAnalysis.Distribution.OpenRestrictionLocalityStatement` | `39d1bdc9cc814ab521d6af1d834fd53e4811c9bb0a4dd3bb39bc9c19432f34ae` | `c4243e0e14a712b1472d9232f2b2a8628c08a68c0bd46b1dc08823f1c96d768d` |
| `HarmonicAnalysis.Distribution.Subspace` | `8febf69fab53435a07861ac994d9ff503ee00b3d129f8308a14907fd8009d6ed` | `cfaca880e9d2e67e4c65d31771d16110114f248e98a6a89d958176ef3f05ac2a` |
| `HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof` | `cd3e6cc183c06b7a1da70531aee94253d172c06e6937c206089e4f70ed361644` | `da1a9372d28aae08cd3a7640a4ae100698a46f2ed83947740968570aff6ec287` |
| `HarmonicAnalysis.Distribution.SupportedDescentCovarianceStatement` | `a6a04de8f4b76f36edab72c579191fea81d7b5d368d2516acd5080f913fa0370` | `2fdcff2e35992e69040323605f3fe875b7bd7fbf36348c37211fe50f7db52778` |
| `HarmonicAnalysis.Distribution.SupportedRestriction` | `32aa52271a5c33ec03fece7dc31446d7d2c921483fc154284e4240ca93c1f334` | `90fb418df2896c456275b16e822aeb6febcb7c73f85b4ba043f9dcbaeef57444` |
| `HarmonicAnalysis.Distribution.TransposeInvariantProof` | `a11b9e9cd064248597fd6a76298775d327f4d3849d9e386e8b5529e2eb0ec002` | `e25ae98f89e029382309352157a94788c309ecf6130f56c96bc9a0d33ba2090d` |
| `HarmonicAnalysis.Distribution.TransposeInvariantStatement` | `8e745c42e89edfbe415e3e41991e54089c9137b445f43015256ed81fd9faf7ac` | `4daaf9de083069a7b42fcd3d00f5be2739d2a36b2abb44456555ec6fa8468670` |
| `HarmonicAnalysis.FiniteProductMeasureScaling` | `6488871d2b3333004f61e454650132961d82e5a068a39db773fd088ce41a8549` | `ade6c38772d3d4868dce5a26a6dee758cddf41084e66c67755e08db7f5f2d742` |
| `HarmonicAnalysis.HaarConjugacy` | `6ba1f6b03479882f2757984a0bea4d686d177252e066428b7f4a277d7f75c179` | `6161009eeed3a7aa29204871307dc38c954ed54f9f95a0b277d05d8417c1b67d` |
| `HarmonicAnalysis.PadicAdditiveConductorProof` | `3ec4f6d56e74b3528c719a1692f1e1a8accfe1333119a8a20359a9ab5a5473fe` | `63ec184c3fe50499e22e280cb6012e3cec5446bd4dd8d9bfbe86e6dc7d864b35` |
| `HarmonicAnalysis.PadicHaarScalingStatement` | `84366b106ce213647dbccdccf6477cf19a01ebefaf549e68f2239424c420b2d2` | `48bf7cd23e6d04220618a8814fb60021d27eea0db5a325f5ba80999f4d7fa76e` |
| `HarmonicAnalysis.PadicLatticeTopology` | `c75b27c8ea60f8dc9d3196eab2ad83228e46e954bb498c84c891bd3fb7357e04` | `1fc8544c37f9c2d6012725b90a5a096e28e5ba095d84248d77f1d0bbfb6bc081` |
| `HarmonicAnalysis.PadicRectangularHaarScalingProof` | `7f7abfe921074321491b39fa2b70c827b63b6076ecdf9076b1a2b442ce674b2f` | `53c72042369b1d7b05b17ffe7654eea861c4c8c7c688d754a5c912eb880d1c40` |
| `HarmonicAnalysis.PadicScalarHaarScalingProof` | `56a5614e6c50f3cce0c08d21118e596550591f8e9f506bd3893598ed04591d0c` | `7f2ba889475ac0cf7ed7f10c7da58eb9994daa9e6a1cb36c7c91690a9d6de398` |
| `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof` | `a396df9503fb5d5092d82a0c29b6d6da3da5fd89b79930f089b25b9b2f8dfba8` | `35e70436e6b65bbd9cef0a84a182c999d4afc2b9d30c1f47d3dece2d49e32467` |
| `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement` | `90e2391227e46c4a178ab5c5ef5cf84175675ca5054277a4371d7b9ec0acc38d` | `f4359e0d9e45b39f453bf326778e01317fb7204c896840ca12c1e43d9cf80b4b` |
| `HarmonicAnalysis.RowFourier` | `1cdf11f05ae24f7860104600c1f2e887f66ad08f211731712c7888c21f6e4f23` | `ba9b9bf04ead5e5c1ab86fe1e124bf3b2c1d007ec2054a410ca6116e84199a83` |
| `HarmonicAnalysis.RowSchwartzAction` | `7f47f12aef414c0b662334e85fabea9a8b021a70875514856c6c99cf7a847865` | `50557cce22aed10aa6eea71218c72ebdd433de378cf2c727379e1d15076f0783` |
| `HarmonicAnalysis.RowTensorDecompositionProof` | `8dc4f76ad27ccb56d38e434ddfa0f5abc1e864e5be0b6ddb5d786be7e815dd1b` | `90253f01060736939e4ae62b6a5a8239b30e293d3136043a74973d8280fbbb06` |
| `HarmonicAnalysis.RowTensorDecompositionStatement` | `e38ccc8bc08f0ae70aef6f1ab27c7e1932a41ef496ff5ef526236086143a6114` | `379bfbbea0afdc9113e706ce79926bcbc060ce9dd7156d446c496c9256864ac1` |
| `HarmonicAnalysis.RowTestSmoothProof` | `e678894d74802a68dcff58f2e648e49d5582157fe9203860c38be0926a165759` | `112a8c9d6ffc229f28a30cce9272a125d7a426eb7724d2b4e5ffb6888a960348` |
| `HarmonicAnalysis.RowTestSmoothStatement` | `f32066004811fd0f950d0fd1e95624d63f844a2a6e1ea30f8f5bce9b84c1ba65` | `d225f88e37ce19bfe0a546241787eac17a78907bc6c5244e6fce2988ec3237b5` |
| `HarmonicAnalysis.SmoothWeakIntegral` | `e03dcd7edf638c5cb6ac30bf9ea73b1fd057c989a17ccc41140db36912cb400a` | `e596812f62706b673582200be86c30c2f48f5d44ebd6c6b560dadab42d8633f6` |
| `HarmonicAnalysis.TriangularTranslationProof` | `f73aefb221d55ba7ea911c211cfb35036a62470d979c797955055f9c1e9fb555` | `12bae01aea8c9e53c72408b3fc15f5232fbb7f278e22dd6e416c6e4b9985000a` |
| `HarmonicAnalysis.TriangularTranslationStatement` | `abf107b9edbd855ea869b75b8585920523405acdb3c4321412220e93e07c02ee` | `c0295777c8c56408003e7f9f78a3eae490f471e7b2a7db844389cdb458dbec94` |
| `LinearAlgebra.CyclicQuotientPairingProof` | `07aee055e8d54a70cae6b0f1a68ef51f909957de1c383688077d1315361cd83f` | `a6fa4c34b639905abc88460f9f5d9bb2980b14171ea94ec95f4add0f8376a24c` |
| `LinearAlgebra.CyclicQuotientPairingStatement` | `dd1d526b6d09dac80d16c60efc917be2461854d9145e82e0cf80280cb539542c` | `718cc72ab42948e69c4e6261391e4829cd38711315d26b29474e0f885450186e` |
| `LinearAlgebra.FiniteRankTrace` | `cef98741853b9598e0bcbe724575c654ff4f6012c6c23fd61ddb8b4a1e8f92cf` | `49db3b5901fbea0b41541cbe71dc6c7d373fde06fff2f83bf21f78d6cad63294` |
| `LinearAlgebra.FiniteRankTranspose` | `18b2cc19c5359146e25013e2c2d26d27c8f512000bd85a229ae661c2714cc4d2` | `7c48270df93a192ffcd73e1732ce3124f96f339f296cf2d0a0fb0c0567c12891` |
| `LinearAlgebra.MatrixAEvalConjugacyProof` | `f8dbb140352f64c5d92afbd51599963b4e8f950bb03e0b945c393956bf08a1c4` | `a682a2f0abc9861175865c17af4e16facc8018297caace67382c06565a33c8a3` |
| `LinearAlgebra.MatrixAEvalConjugacyStatement` | `ab2e0e498ad058baa7cc2594ee41686d77dcc38e28d67e5cab1e68f40fa9bf7b` | `745cb977f64ffea9ce091121664e8b39542079e1e1751125365b355de6977fc1` |
| `LinearAlgebra.MatrixCharpolyConjugacyProof` | `0d0dbd8ecbe3f0b6c357aca66d929543279abe90461c9e84006b027f71487d61` | `9f2d123a29ec65636a7b3ea943217cae407c6f8a16f32e29e395d0e343007042` |
| `LinearAlgebra.MatrixCharpolyConjugacyStatement` | `6e146d9fb962edc55142436b4685039d7379e67d6fda8e024be507774a0b94bd` | `4b498594e3e59339696727f73b6c33f9086646dba0c0f5795b7cc33d618cbc4e` |
| `LinearAlgebra.MatrixTransposeConjugateProof` | `c2b047f014ba6ed78763774cab1457c586f6cd5900b402fc2089ba4ff0463f5d` | `e1c36ecd35f3c9475cf84380b05a3fa7cbcb7a2c77fba44a5cc1148874a98722` |
| `LinearAlgebra.MatrixTransposeConjugateStatement` | `fcae71df20375b0b99f55960229ce92d4acbd1eec965ffc9950b63b7aac1e87a` | `809ec3e3c1d714a1b0acf2bc9e5bb5bec26d9174e702f41de67639f4a555edd0` |
| `LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof` | `da0eecab15db868ca81c3d761356fdffa167c38139402a107bd79c742e4f7242` | `565b97b7fa2efc757a11c4db8a2e8f34e08e2f11d23f4eef6f869773f416c3ec` |
| `LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionStatement` | `227007b599977c51cf292bc9e5ee59fbb5e070d311d19195c83ce14a59dd0344` | `43c05c0f9211f7acad230cadcab4e54ee536f04373fb162c938701d1c5397a63` |
| `LocalFactor.Euler` | `30ba4cd130f4f4d574a7d5da171506ba0fb9757bbf5a076de02bf7627c467d76` | `9c8b179437770bc6d945ed19ca31928497e89b5f810f70b4241238853f9b7e9d` |
| `LocalFactor.Euler.Definitions` | `6fde12cbc1ed3f8e6e184468f5edab01cf1e597256f06234e0e6d675f1ba617d` | `825e24ad0de0940e5dd5b03150e35a910a1cd2e5168fd65b9396088d5b0d5835` |
| `LocalFactor.Harmonic.Statement` | `1daa8305602e7162c20fe612295f15403e02df81128bc299cdcd7d17becd13c3` | `2b93b69d51d8c999c7fa09b0468e87ea428651a939f51c602ffa9a26d26c4f5d` |
| `LocalFactor.RankOne` | `94d67d384e29bf7a454c3a243912c46d19634d9979a54f10c4db057c424ea5b1` | `58a66cb7531bfcd6cf59a5a143a86d5bab2c46c4813e4e11004c97ae2931f80a` |
| `LocalField.Canonical` | `e702bb7808fc344bda47a3093d9438d5cda71dcb165be7110be7b393f61d7c48` | `94a7a93a2ac19a6c106542cd76530caf8244892f29b98eea8755b031ec7e872d` |
| `LocalField.Definitions` | `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517` | `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf` |
| `LocalField.Normalization.Definitions` | `b997a64a0f59ce13d45e2b5349de9ad87466a5e2d3e16ab3f1a4ef97a048214b` | `dac7d3aeb5229c505e5271f66d7decf6c7c4404853e9f15a363b4f9401902436` |
| `LocalField.Normalization.Proof` | `4efa0826ddc069b2963ab4933716979e5bc7c5c866498047aabfbfc417071ded` | `1c3bf219eca92cd04af13c152757d83b4d92dd9787c334acec773bb51a4ad161` |
| `LocalField.Normalization.Statement` | `27f6b841c15cf1e4dffcb40126f95ea329c08d91ab9950d8fe645a94683eedc6` | `245db7bd9d6b10a8e9cb2882021f2d210a396aa1149e9a8adeb9a889bc7d753b` |
| `LocalField.SmoothCharacterNormProof` | `22c32d129af2068dcdccde16758604c6a08c54368c8c95005cbb5c81c80055c4` | `e2dbdb3711a816849d0a9963ca872953b99bc721386505bd92709fd6b5f772dd` |
| `LocalField.SmoothCharacterNormStatement` | `7fe661b695a6d1a122d08759243ca03bf6ffdbf7e5a5653aa71f6f82e4a5cf94` | `bbc047876e9e067f727e445347cb2182aae602d21e281aaa2fbbc537eec9239c` |
| `LocalField.Topology` | `09ba251eb70a2455da2a7864c7cd34739adbfa717771adc3a86670d2bd0d791c` | `1c28337c12f885cb438b405d58a077c186b4710d20a1256dc0fe8288b4107992` |
| `LocalField.Uniformizer` | `311b6b6c95c53232b2582e6c769184d64372da393b3e2c9eb47bd43211992efd` | `ab000f42c552fbedddba4babdf5e25dcf7cf2ef1dc77320bfa85199cb4c35713` |
| `Representation.Category.Abelian` | `aa7467474aed61362ac0fe82c32d16d989f135671099784fcff0fc25beb5b15b` | `97acd1c1cb0369d89b7a53374f1fd633203a54330f7dbe7caf79ffb48d32eae2` |
| `Representation.Category.Basic` | `6a4781890b642e590206b68b7cea02bc4add8bdfb85e6a29991f73992bbcf706` | `647da2c8e2011decf8c6971c0f4a20a162e6ead265bf4d7448b2045072862ba2` |
| `Representation.Category.ClassInvariants` | `4f65d38d130993b4310a63e60060651c60bf8178ab60000c37e0e237f7991a82` | `058f7fbcfcec69db14bf4a4325735a14cac4637f74e49f9dc9c0d6c47b11f8a3` |
| `Representation.Category.ConstituentDichotomy` | `d42059136cb4167e8194da6b076c201dbae665d3552ce608c14971f903c72a42` | `836ea06e5a1e733f8f7e88d70c3bb4d758b15fa879054293e49c4daf64dcc901` |
| `Representation.Category.ConstituentDichotomyStatement` | `2a0d8209646c70772c85b598915fc288b823b9af0cc38d958b93fa64e52772ac` | `7710c6de008b2d00d788e85af65625d4401695b6376e5aa0f252e9e05a999bd2` |
| `Representation.Category.Contragredient` | `9dda8c5bdebc24bd1df588be1100325dffa275d649dd258f9d978bee5a8723b2` | `a370e601eadc42ef41329c238106587a5be205b10431fd19bee509a520f56002` |
| `Representation.Category.FiniteIndexRestriction` | `c167c3ce3092c5d1dcd0bfa20bb561cda253825cce3036214a7376561674cf63` | `e6d89c4acbee37c3dab6db997e500cf58544ec61c1049bb2edca54d9d8ac34f4` |
| `Representation.Category.FiniteIndexSemisimplicity` | `c42c94b588ec7c2ce85107f088260b82f21b0b6db2309caefa6ec4eae3c69402` | `59097a3872271617f1c395cc262677271157b44e56efc27f54633b44cef30c6a` |
| `Representation.Category.FiniteIndexSemisimplicityStatement` | `5fcdce9588ceb3f0d7fe7cf2019409a3ed1fdf38354e4a302d3df9238eefb79e` | `01f6048c20106816af64d8e09f156d65fbf18b564e4ba18c2002be01e9d7afc8` |
| `Representation.Category.RestrictionSubquotients` | `9f98bafda22a800b54ee718bd51549dbfc703bc7385927db502a5026097c232d` | `86817697d8b872835ed0b115538e93bf7674433666f08d8b841f89b0e6bb986c` |
| `Representation.Category.Subquotients` | `d443366e944c46fad3f3ef4e82e519a30e44d1b5194c829b795d9fc1a6c531b4` | `9ebebf01a99db613b0ca298928e6a479773819216d81de9506a8faaf08860325` |
| `Representation.Category.Twist` | `9fb1bca986f0a1a202a4e3d9e1ac481405646293ece6da63374e447cd85ca740` | `e16d708bc3b312c0a79947852bbf147ea230b0a9b8b9ddbd9f80432833bfcb5d` |
| `Representation.Category.UniverseLift` | `75b3de851fc0e729d2436d88cc885b7c12b1b2029a14cbf0f7bbddbf79c2c817` | `f7b08493a02aa756af96799b4b8a1be94dd49e45df671acbac781ff36a150502` |
| `Representation.Character.Basic` | `3fd0190b469710b8b57f46c15c5059da7ddb0a7df2173fa2804c365891ea81ae` | `c4d0a1cf58ff6a46868dd7c126b91406fafebb771ceca1a91b7c1f20eeb524ee` |
| `Representation.Character.SeparationProof` | `2a1fe2df71425d9586dfb77784ac23fd1045300db218de5c145dca7b8febaf5b` | `7ab663d4678b7abe2f079980ed245fefac034d849402bbe947cb0cf43db04ca6` |
| `Representation.Character.SeparationStatement` | `43ad78d06208871dcb33cb508bd3c44d65cbb248a943e5b1486b0c3c4a5c86be` | `8e79ec8ba36d5cff705455db237c0d2ae9eedbddb6466539d7a4e23825fa35ed` |
| `Representation.Character.TransportProof` | `67dbcf3b1e85e85cd2f329af98442de26110531640a473ad178c4e26396aa023` | `47871bc1b4dbd5924bcd26a31113634e70a9e3bea0c63b684e6699373f5cf1eb` |
| `Representation.Character.TransportStatement` | `e2a8e9173a9f1f7df45b4a22ce69b093852d0b8507167fe464cee07cc4fe75ac` | `43e1052bbae59c9978ad86fa9ac227cd4fe96a5ce13ea82ff7e8afa2bb0591bd` |
| `Representation.Classification.CanonicalConstituents` | `3d928c04a8b8f9a8dea9eb52f4b202d303a8f474372e8fe1b4b7de0ced9e1d97` | `7c2c55ccb0c35c34405d4c61bedb253d8a9f088da308585eade4ecdd096e616e` |
| `Representation.Classification.CommonImageMultiplicityOneProof` | `c19e8c64cb3c8d6228761b2aed69ebaa50fe285844b8ffb3ad02e1fbcb395edd` | `22d5cf398213638f61a0d4b194c569eba5d85b7b77c1b3aada8a21f07a16325a` |
| `Representation.Classification.CommonImageMultiplicityOneStatement` | `d00f9b03aa344e2f5ee39b54e86df05a5d4ccf18597bb6ade809bc18178c80fd` | `e85404d911a0c5caa930cddb92844d3d00ceeb84c5276e739080508fbbf8132b` |
| `Representation.Classification.ConstituentCompatibility` | `e89c9a11f926900f00a05b6d69fbfecb305a4ef6f6ada56fef9c61cfdb724c63` | `e051971cbead9825bb3f3ad481724ebb767312468bf19f033fd055b3a2919011` |
| `Representation.Classification.ConstituentCompatibilityAlgebraicProof` | `b56de7159b58c1ec309a8f8de9e88f075bcdad680b9f3c37fc8ae1ac4b52bcae` | `e3aa163d57ddfc079d410a8cf27b0f5041c362bb3e34e7eacb80ccde8154aed4` |
| `Representation.Classification.ConstituentRelations` | `deb56924ecebd5c12a875ecf69f4b4960801e3ed6df5d8fe013c9a303cd58721` | `47047bc2be3ee74e4be6e5077319f06c463d7e446b586f7b3d4b58e016d8641d` |
| `Representation.Classification.Cosocle` | `8b7168578343ff57b4b156b368cb6766bc72c7846d38e0b7a024e6c170269e2d` | `f5449414ae2bcd42f75b05e3a6b4be70ef88f3eaecf7a7d3488ad89fd271ed4c` |
| `Representation.Classification.CuspidalIntegralTwistFreenessProof` | `91598de302fedc32f669d5e32036bb2993e70063c2db308b93398e38bd14aff5` | `59e14ef1fd2d7fa36f55558ea272239aff9a2b065bc2e3497074c64335c85aa0` |
| `Representation.Classification.CuspidalIntegralTwistFreenessStatement` | `e1203547aab90cb91ae335176fbcf4f57b6fc19759c4ae12b04f85df64f9d0f9` | `96af8f0c54cfaafd99d4987f50ad41201e171bbd67e4124ac305eaa694acfb5e` |
| `Representation.Classification.CuspidalJacquetFunctorExactnessProof` | `51acc4c02231a68ecefa28809c73b0ee34584dc46cd7d90c38dc83ed5856e1b4` | `66fd1ba3b50e7825a5d6ae61d77372e8129d66617fd922150f3cbc8019ddb493` |
| `Representation.Classification.CuspidalJacquetFunctorExactnessStatement` | `58d376c10e81d98152935c374f195b670560b11153d7c0d281966fcfa97907d6` | `050310ff1ef01dc55cfdf40f9f93895387c17dcf3d1f0476ca8d1bd3c76406f8` |
| `Representation.Classification.CuspidalJacquetFunctors` | `59bc704c7b39caa770aecfd1d65703c9e36593c0d0ba2cca1a9f670bdc2315f3` | `938f245d6f2f2f3374158f9025bf26cc3abd98fbe53d9333867d84ff63520916` |
| `Representation.Classification.CuspidalJacquetMultiplicityProof` | `e0d80552aa3eb3dbd82452be0f55ecd7c3be3d0704cd0f8d4c9da43a47fb7397` | `b69555e4568163c20a97bb96eee35137038a4552b42a49168b7d4c8bb9a1233d` |
| `Representation.Classification.CuspidalJacquetMultiplicityStatement` | `0adb72d788d2ac848e510f8a6e016f2a888cdf95e65f023d60f67c248421ff1e` | `b5395e1f4a3143c89fb8ab794b7c2ae12a0832aa28b98074edb6fb1f00a4f6d0` |
| `Representation.Classification.CuspidalProductContragredient` | `5f2e33bf3059d19e2431346635c0e979f2c2c7a38245888e52c04fd7374a2c47` | `b03e35f0850ab297e413a963257305b59c49a72317f7ff8696331c192025eb28` |
| `Representation.Classification.CuspidalProductDerivativeQuotientSupport` | `57917fb9df2d4968ebf6ad877fa7ffbda60b29359ef9b89e79f8673e328350f0` | `97f7ec47a285450f8286df774bd96007924459180ebde96a0eb90510554e7547` |
| `Representation.Classification.CuspidalProductMirabolicSupportShiftProof` | `0800617709e1c9cb333eb3463eb65ee234960d39cf4d1ba299a6d4d6f5b730da` | `8981eb0a62eebf50c0d2ce47948d22cd60ac5ff2c4a2691bc0edb74ba59a2c76` |
| `Representation.Classification.CuspidalProductMirabolicSupportShiftStatement` | `464668154b647861a599231a4f3fb23e4a5ce96d08b36b2a5f1d1ea5f0612606` | `36d0047c2be4999cce1f174bf87594feea86f42216012570acdc3ef15993e0b3` |
| `Representation.Classification.Essential` | `5b770a6b25f81dbdcec736820927a53edd84fdca0667ba8706211878cac124f3` | `2cc6ab837a1abdeb9591c4f29a2c57e350c4eb6eb7cbe9a76bfceb0c8e8e42b3` |
| `Representation.Classification.ExponentFamily` | `064027bde0552ca913f5068dd2b82883bd4d02049d2a0ff36e1c6549244b382d` | `6586b37df79d48400301011f4c0da770773dfcb66f18dd68a06ff149542a9144` |
| `Representation.Classification.HeadQuotientCriterionProof` | `13a22ea328fdbf7e4f6ee6f4a8f5a62299744f8127da09614103428b4f74bcb7` | `57480d86304c63944d9529098e9c6ad70868712c86a186b8d5d6856fdd6d49cc` |
| `Representation.Classification.HeadQuotientCriterionStatement` | `3d3dea109a39cc4d38739f8d188c6949dd5ec3c94b28f916ee23978769705b67` | `1d9f840e11b727dbbf6a2bdc56a9ca33a91f8b0af6dfb6dba22c6948e2594f5d` |
| `Representation.Classification.IrreducibleProductEmbedding` | `0a999855052b3dbbaceaed17741d151b354627faf3004049c9ce58232ef00f4e` | `2c581f724e233c558b874480ef5d4c40199dc81a763f8ddd12590787c7330f0a` |
| `Representation.Classification.IrreducibleProductEmbeddingStatement` | `15aae2c06f59c603bdbb162faad33d14fadaf462bb14429dd374b21492a052d5` | `a6a9843c1f66aa4d2e83595ec35a40315c3a84d8c30d7d0b03924e578831b709` |
| `Representation.Classification.IrreducibleProductFiniteLengthProof` | `a33e3cec646613d2850af65b070ce61e1bac5f15cb2f27e5a20bf7939286e4c1` | `2dab0bc3ddb209af152cf88ec9a77551618eff1bcb77f6fee8df23e26fc3c0f1` |
| `Representation.Classification.IrreducibleTwoFactorProductSwapProof` | `a1182080fbc3caef019dd56602b42f3c0be79fda3e561594fec2271b64d2f766` | `2137cc00ad533534721e23b4add8aa3acb5242154e88cb0c700d2da4baaf7e19` |
| `Representation.Classification.IrreducibleTwoFactorProductSwapStatement` | `09d563eb3211d353fe4d6139a3909af1117268f6965243b3da64f833bc08fe0c` | `616fd46311dafdf11e1f91023139ef1192c0ca82af7d2476765de3a59e193615` |
| `Representation.Classification.LanglandsData` | `3678fb721704683c1bbaddca5c363bea2fe96d462c0f2c2cfffdea7ab0f1f525` | `78cfb7c8dff33176acd8fa462762677fe6c4d521b7a495ac9dfbe76015763ca7` |
| `Representation.Classification.MirabolicDerivativeContragredient` | `61e3b52c77ba3863d622973c34e40a581882beed6fa9b42099c497972a9d63ed` | `0a6c30f0838d57e3c5f2db5b25dac68944650605073068dbd054d774a7e568b7` |
| `Representation.Classification.MultiplicityOneConstituentProof` | `17e938dded92d7d335b7ff15e4ebbc8db723d8b5712d2b40d629a91c9ae8d1c3` | `b80ad7ca453bebf8c20a10a5d719482df81eab0b7080bdf035820bec7520c40c` |
| `Representation.Classification.MultiplicityOneConstituentStatement` | `5f99c7d8bf8ad9f008bdc3321fed3a42ba673d429689c76ca9514b064af40d0f` | `d12c43292456d9a5a346760ee9931ba8a973b7a7635cd81b7f577b4317fb13d9` |
| `Representation.Classification.MultisegmentClassificationStatement` | `639faca64a0ed605c85b3b4629f85dcbc5da336c4a13219c854f88a9a7c7b182` | `1691e3c85c5024496e9c4621c11468423a88880450057eb7d68677b1c5d9fe5e` |
| `Representation.Classification.NonadjacentAssembly` | `6954ed1a7b2e31159febedfa5cae21d7d08424a18ded9077b04f44029ea9b091` | `244a4bd721758632e1856988ee6bbed731e607c4ac3282f3328fd971ca386f15` |
| `Representation.Classification.NonadjacentLeibnizPieces` | `c9465cc65a26c2866d141fa3fe1f57d7a8353c660959d81f10e71aede514d730` | `a0fb0260bbd8cf22a3c612c347e20d72c01ceeb90db65f2576f9e153f4daf5a2` |
| `Representation.Classification.NonadjacentSpecialization` | `ce07a0d033331cf866b49a230e2738e72195947c0e78867e7ea1d469da8f39d2` | `e8e54fc1a5829ede79bda113ed61848f50458315680ad97144c9af9a27c46e19` |
| `Representation.Classification.NonadjacentTwoBlock` | `2f12c73ea7b386f2c063f6296a591d0193efa8f35c264aab535607fe4de23d0d` | `9df0d6f41b59a9067e1839d45bac8ccb4a1351a376762dcd96490e3659932138` |
| `Representation.Classification.NormalizedProductFiniteLengthStatement` | `ad77de724ec74c75a6fd349b61119f6fa106adef2bf204f28d26c87c70ccf6b5` | `e428d95b452fadae47625d55cdd3b3ce89fc44292547de8f57c3631e982830d5` |
| `Representation.Classification.OppositeCuspidalJacquetFiltrationProof` | `7b8fd819e58731644234bf647893a399142238a61e40b0e01363744488450e9d` | `da3543bdaff230cc49f8001d1445d0d5729310be08e0eb3f8f0bdfabe9fe9f59` |
| `Representation.Classification.OppositeCuspidalJacquetFiltrationStatement` | `5f94c4af13a640d09c7386afdfd849091e5bcee7739cec5107b82c524f5b9ad9` | `ec158e2534775abf8ad13d1a853db30589c59db9075df568f394717924b5440b` |
| `Representation.Classification.OppositeJacquetQuotientDetectionProof` | `ea19caf22aca2400667311132f0bfe0fdf8d721dd9b1d70237e6c64dbfe0d055` | `5d5e2e80e0f3ac1d60e3ae2da3a6822d04a2eeef2a9d57a098b328683659a7c6` |
| `Representation.Classification.OppositeJacquetQuotientDetectionStatement` | `143d5cf5534d4b4d0bf8d48821a1347615da4b48d354e5423a508ece1fc43558` | `d87c5f0e0f0fe18fa0b09ae3be6d7a5786f4583683209d1ced3463b989d2d61c` |
| `Representation.Classification.OppositeJacquetReciprocity` | `7bce365f30dc3cfaa20c9dc5336d6d048bc6ceed3bf5a74e052344b627973360` | `d854c0c5d8e4b17f5b26ce124833432bb12893c46bad49bdb3d5130e23cdf328` |
| `Representation.Classification.OppositeSupportJacquetAdapter` | `679049f9a9463943b80b6d10d92efac92b92760d913ac8864ea0e728a1a2453f` | `0040a2bd5eed25a64c1f89f8c4525a0d122ea829cc3ae052a0292c9d25f57ec3` |
| `Representation.Classification.OrderedMultisegmentHeadReduction` | `1d6a47c7fb3a80cca62e76927ca16fa01e58f70bf69bc11bfa4d94c69b501be6` | `e11bf55ec47ed1bcbb075632f9c49b2c871b6541946019148e3d6381695c80d6` |
| `Representation.Classification.OrderedMultisegmentSocleBoundaryProof` | `cd2576f91339a46c7d671d6d4cf8ff20af437f4fb39f5d903683f1eb40354381` | `37d84723778bf51c9482c647a20a7ab0334c22e8193b879f0f6b16eef122fee3` |
| `Representation.Classification.OrderedMultisegmentSocleBoundaryStatement` | `2dd550ec829a9a29b2837092d1d3057672f5791c33066c544cc23d820e884482` | `a533e44ed0a9d377671d7e098e8948f492337161b0f1bb60b0439a1216821cfb` |
| `Representation.Classification.OrderedSegmentSquareIntegrableConversionStatement` | `91977df29d091b6bb2637a4d0b491a4003a29d06d746b12005443c4f1bcc2e84` | `2827d5e17f74d921ed623b2e324fa4a4fd2197c8c0f7941749585c75d0815749` |
| `Representation.Classification.RegularLanglandsHeadReduction` | `557c3a293f63e1530b2c8b96ba8752742cbad21dd8cf8d86b90edb37313e0b5f` | `5f02a0e528369339b427f546da9aa998c20344b54e30ce40900187646556131b` |
| `Representation.Classification.RegularLanglandsStatement` | `ce6da19d4d611e50551e31edd5404f4d83d14d90a645d6d00b5cb26d26d7e352` | `c45725c3faf41a59d39c5d0b7197849226c8104d277287f0150dfe1f1b685f62` |
| `Representation.Classification.SegmentConstituentCentralCharacterProof` | `beff1d4b955f46f2344edad55ffd47e39e8dfc5fc7c13871289647baeebc9f38` | `e318d93a52d2915a2318fe4142e5d0ba2167c37aa557b49ae2fbe25e75dbc769` |
| `Representation.Classification.SegmentConstituentCompatibilityStatement` | `0efd1b50ee4894259c2fa698529ec2976494ab9d825cdd2a71b49390873b0338` | `62d19df82ed6ef5ff3e917182ae1fd361b408c1f6e4ef8af9493d9ba10a0faf7` |
| `Representation.Classification.SegmentConstituentStatement` | `7639f8816b3e05d00203be1a25093811a5b7d6b0b02026ade3484aa2b08c4ff3` | `cfed4fcab0337dc2870c97272b78fb18ab80759fe8efc71a83ec3bc5c2400aa3` |
| `Representation.Classification.SegmentContentShift` | `d17af92dc47d552de0918397c87fe7cbde9ab2db919609fb33d873c10ff718be` | `1a5e89b9592323c5a3b593f25b2b75af220bbaf278e1d638b5ba37513e4f31f0` |
| `Representation.Classification.SegmentCuspidalContent` | `fa3106351b4a1b6202a2f738e30c4f6cb1fc30fed0e9fd8257ee5e8ee2cc6beb` | `03d7270a5438ed362293f849026d7442b71ebdf80e5f1b68a8cca47eeee01642` |
| `Representation.Classification.SegmentEdgeCombinatorics` | `13a3c9b429e5339ee76dc0e6cecd8221c0503407634c26e85a292ece8a7ef25f` | `232ac6e647886c9b3f6fc38bb23d19c5c54cc389e6c308655270f6636274f197` |
| `Representation.Classification.SegmentEdgeFactorHypotheses` | `e256004085789f92e7410622e8ce91bc3798a2dc4c708f34d41888111f22f514` | `c15a7093ffdbd14eadb95f6dfc8ca6aa3399d5a9fa50e7c5c0b0cc665f21e815` |
| `Representation.Classification.SegmentEdgeFamilyHypotheses` | `9ae680bf32b58e80f82432d2138d068295ec62358b833ac74381f63ee24ebaa0` | `e983690771bad6429e9e0c548cde44632de1568e8118bddd65a64382394f3507` |
| `Representation.Classification.SegmentEdgeJacquetReduction` | `5cfccc87418f58bd1b32edcd9cbdd051be26527d7423addf677069242d14fe60` | `b31ebbdbc396f2b94655895f404b6876d2a43dc24b1b3e9f22ebda55d220c95c` |
| `Representation.Classification.SegmentEdgeJacquetStatement` | `a6d13a65334eef45c017d805e4665c47a6f63b9e1c46495369304db22f319811` | `672927c6f08e8808bfd2dc744c8f8b8c0852cd2edf6c8cbb06dbde11a3a36414` |
| `Representation.Classification.SegmentEdgeMaps` | `e09fa1a0c83e13fad249e581118c8b757c502097d8f061812bf134f17f12b0c9` | `9602cf2e52efe9e76f7be6db1a7eaf51b99190d6eeae707b2835623ecb5169a2` |
| `Representation.Classification.SegmentFullJacquetAdjunction` | `f64361996c065f48a5c818f48d12fb76c6fb8eb42286cd1e4253e38323145a3b` | `bbc8c6b6fffe9ba1a4d1baa4f160caad6a75f2e532f68ef72f9155a6bdce85cf` |
| `Representation.Classification.SegmentFullJacquetAssembly` | `312d0cf1664353dfbc6632aea32f6a2b8ab2588ac800b1f6aed2394fa51a3ef8` | `1048a80bcb17c13114c453b6972ff592465db281c2f5bba2fcebc0a3a7cc9c4c` |
| `Representation.Classification.SegmentFullJacquetCentral` | `e3eebfc47b743204c7942c28bf6fada12d888b744985b5429e4060757ee0b77a` | `01ee0c72ac4125faa9c45248886d63978112ec42c3b69a07ef468c4a42c7bffc` |
| `Representation.Classification.SegmentFullJacquetEdgeData` | `1f39db60d5675113dfa7994e951b319ea396a5f7d3fd252cd6816e94fc571c33` | `275773a605aa92449d819bc5328a70d55d96d58d138f899c7d537ee091a6e5a3` |
| `Representation.Classification.SegmentFullJacquetEdges` | `050064e2768e1d9e389901ae599f870206ddd762b3fbf966466d3abb7827df05` | `ed3c7e75bbcb66020b6e857828ebfa3c66c96201753ca6805f62f3941ffa283d` |
| `Representation.Classification.SegmentFullJacquetProof` | `4564f0d3991e46b4f0ed603e043b4dc289894c74996821cd6b698b4ebb60f5f1` | `c565b07ecb1eadcee27c6297cff301056a2aa635bf41c4be9f52a315a94d1d74` |
| `Representation.Classification.SegmentFullJacquetSplitting` | `db6fbd8c8496d561cc9cc4b5f6a4867764d4f8b2eb3026b086c12dbb4671fdff` | `0c7050e5a1c2f12b43121b16cd326f3b71c621ff21845c912cb0080d7a5b5c35` |
| `Representation.Classification.SegmentFullJacquetStatement` | `321f01f1992540e9eeab25655730358ec365cab3971ee44be0803237a0fac97e` | `8353bf6685de3b1aae59c3b31fab2c962f4f7f1d110f27440dd82e8b00c1b160` |
| `Representation.Classification.SegmentHeadJacquetStatement` | `bf45bcda5b3f1a65a45b6c452129bf46b42e02dc33711f7c22a28de7febfe4db` | `459c2136807ca4432e18434e9bc4a1496f7199459110afdb8950ff5f86de350a` |
| `Representation.Classification.SegmentInductionAdmissibilityProof` | `7fe3133e14ecc702fa2d1b26d05f1dc888ac8f645ac99a01740a7b434c2388bd` | `3d7c2f74c8e2cec8e837c210abacf6ebe853ff92b01da2731fb0edea0a64ae89` |
| `Representation.Classification.SegmentInductionAdmissibilityStatement` | `82cf43a5f958647f4cbaf777ebb1cf38ee70199cf8e84daf61adb06fb04d51ad` | `30f433bb37fad406fc7422a2c9e830f5a86c4c7e1749f7259e54db9b764ac07b` |
| `Representation.Classification.SegmentInitialTruncation` | `f5f9df68fb96b9de28263ffa9fe0e2a23537edb87ca18c24cb10460ab4178796` | `29c9f0c6bc0fb06ba29d96dcb430c86ba2594257e361951411daf98e53ed1b59` |
| `Representation.Classification.SegmentInitialTruncationOrderProof` | `ff85402532985c19b2bdb67f2f19e2043b9bd2386cb21fa1b924a86920e2a95d` | `63a72b0a4fedd0c574b44c58ac7f779fa5380fd1490817966719f8d98da18871` |
| `Representation.Classification.SegmentInitialTruncationOrderStatement` | `d25131cea95fc7251c13fe5a2ac59d23f26c8ded703a7b6ab630d1eaa78893da` | `6f37f85fd257a009c5cade95b1f550009e641022e7e05b3bd5c9ecded8a768dc` |
| `Representation.Classification.SegmentIntegralCoordinates` | `e76f49872b545028b8e9f7efea4fabfafff90c04a8b51597290e7b2c81c2d7a6` | `97003eb0a2e21659adb0e203c5a2b2b375522263b50c4a4964dec589b2e06374` |
| `Representation.Classification.SegmentIntervalLinkage` | `3b48374b22d94ad9821497c145010f0e12f2e4270afee01739d6a5550e29012e` | `b69168095e845dd646962c2c1d35dc9100d0ec2e986afaabb58822d2ef3c3c15` |
| `Representation.Classification.SegmentJacquetMultiplicityProof` | `ae261452804dfd04d3fdd31635162c01f9c3032ca365e24ae3bb159962f2b3ff` | `fe30119b9b78ac01f1dae0687a64e1f0d763ee9f1facee0d911a1082ce851797` |
| `Representation.Classification.SegmentJacquetMultiplicityStatement` | `43dea26db7a0de03a5c49bc4bfcecdf67c7af0beebf3b8646880fc744c972868` | `dd1d12b483499f31228ca6aecd26543958b358e6fe9a494f4fbcb168a485f405` |
| `Representation.Classification.SegmentJacquetReversal` | `20c69d78ba4b390dfc2c6d1e48ddccc5253d0193c2bfd2ba68f197032186cb15` | `34ded6da688d90fda3533c72d12b888652ca46ca5f953b035cec9686f59a81be` |
| `Representation.Classification.SegmentProductCuspidalEmbedding` | `27204fa93c704243ab405206b1dd6a5ff9041b8be02ac7e5379663588917e960` | `e588fa60ca9ce11fb1b0959d7c0c76da1172616091b8a5d26535afa2aa3b36fc` |
| `Representation.Classification.SegmentProductCuspidalMembers` | `a58bdc9e63960cb4e25834d57341c8eb80893f174c0e8752c1b8767d2655f402` | `8357ae42a309961fcdb42ca79bebf9ee042ec6e27133ea984137f084aaf03e40` |
| `Representation.Classification.SegmentProductOrderedAssembly` | `cb17c65af83f97f3e2034585abce881141dc53acb9ca54a82ffc68cafafb2fc9` | `765af9ab3f4d304505e984db0ae01ccb7ccc8bef7ef7c0c933fc77d1610165ce` |
| `Representation.Classification.SegmentProductPermutation` | `5d848fc850632902c5d3bfe3ebfd43710214f060c23543b3b814e50ae898a375` | `dcf1fc212829d66a05f741b3e2a9e1c645980da950996b40ce6ee54d760b9f2f` |
| `Representation.Classification.SegmentProductSplit` | `35aa2c40ccf84d449fc3e828bdc95b9ccaf1dbeb13c6b6a9fdf4ab0b81f87eee` | `3db1abf4c5fae49f017bca03177bc49114ef063c22b9d77db704363403edbddc` |
| `Representation.Classification.SegmentQuotientJacquetSingleBlock` | `08874d089a059873256a4d8208bd7f3f3051e65adee986bf28afcd941c20358f` | `7ab1622ad46ddad8cdc32f2b0d0ee4ca8b01a8aa12452c49165582d6dbd16550` |
| `Representation.Classification.SegmentSocleDerivativesProof` | `d44feaef7d07263c5a2e97db94f40445fefe9ec9ecfff5bead70603eddb8b788` | `95ce5637243a91912e4b1ae938520bbeaaf6edc01ec208e4c4a9d4b03d99b8a6` |
| `Representation.Classification.SegmentSocleDerivativesStatement` | `5f74f9e0854bfc4bbc382bab1b3f8e30a6bfca302fb5b90379742342f9c41295` | `b59dd44752a7dc46652c7bd6aeca795eb8b9bf654bb7940f005fe45df4ef0ac3` |
| `Representation.Classification.SegmentSocleJacquetProof` | `5a7e16f7b7b2f8bebc835a98350846d220ac95eccad9523a2ec08843ffb1e0b3` | `174c8d3dec88dea90d54a868d79157119cf875eed95cf1f80b4924719aa89f49` |
| `Representation.Classification.SegmentSocleJacquetReduction` | `f317a3eef99dc679ee7cbf20e123f5b7433f049b58537fe0456f4e23e09a09d9` | `47af57915f06dee730d910fba9b6223c4a1564d8bf25cf15a148c95302946beb` |
| `Representation.Classification.SegmentSocleJacquetStatement` | `657cf1988a8b11c320193ef9cc688d8654b1a8ed7b605e2b3ee76c4361054ba9` | `2f770f44763f673e65df2fa019489f9eeff8944c95ea2c61672567d8bcd74b2b` |
| `Representation.Classification.SegmentSocleProductCaseTwo` | `fd776b6ffc04cc9920250d9f1fd8039cced193aaec3a779de2fae36965c5f924` | `b097e53f3a70d3ca4d3a7cf90010b961c739b79e6e75500f036f27788594fa17` |
| `Representation.Classification.SegmentSocleProductData` | `00b70c5fd0354b3bc6b81baa92d6e4809a801d19242572792c481c71ad7c9c02` | `39bf46beefecf1eee738e8f283e02bceaf31e5a6e678dfd48b2cbd497fb2d24b` |
| `Representation.Classification.SegmentSocleProductHighestDerivativeProof` | `d18191a27a92cd827bfa562d152f404e788d51838fdc11a53029403f9f64d514` | `83e97a69af86167b41dc7ea0e4ae36e1556af61272f47464c2e03da8c4aa3d62` |
| `Representation.Classification.SegmentSocleProductHomogeneityAssembly` | `8b4bd199fee84b985c084aff9354dd0433b5266abe25fa3d1aa292f2bcca0868` | `da1866ff3f06b2774d263f1859ae35d102e6e0f952d2ec1fabfcc3517bf1f2b8` |
| `Representation.Classification.SegmentSocleProductHomogeneityInduction` | `3c6a5d9cf8c4bbc35d38ee06d00e2f3534601e42204c0aa28b719af430515c96` | `32bd5f734aba0fd675cb59b884d5a245ffd377e91070808f351a9c0d8af879e0` |
| `Representation.Classification.SegmentSocleProductHomogeneityProof` | `84e9e12d67f1356a20d90bda6fc3188fc60ee91d534bd4be819eef919246a29c` | `0b7f89e491600ea722fd89333c95ed0bd64ed97725cfc6c588dab24d5a25acff` |
| `Representation.Classification.SegmentSocleProductHomogeneityStatement` | `f36937bffbea3849a74e0a6522b56058423f7ebc2d9f47de67d15c80d8452d70` | `8edf866b41bb54ba0c35ec97a4244c005c23697f0385d6be0f18191d28f040ed` |
| `Representation.Classification.SegmentTensorReversalProof` | `8763c7766b2e1df50f3614d1b3bf1888e5d47d36ab146f6a4723821343fe31be` | `a6ac8fd23324c240f56e5f3a7f63c8a431587dc533c675f352e23f74b84c4e96` |
| `Representation.Classification.SegmentTensorReversalStatement` | `c03d2cfd3f2a4ae109faf85f8a44ca0cf8481578abbfd6169e9c2833763a6d03` | `59311d73d0fd22b78720407f5138c4a17f5205e7b424c21a6cb5114bf7d45077` |
| `Representation.Classification.SegmentTensorStabilizerProof` | `85f13c35cac5b5f1247d8ff9282ade2b2fc6607cf317a15c56d86f72d4efc108` | `53ccf2663d85ba3e8476d40a45606d67bcff79c77fc6bef14ed59cba198bae48` |
| `Representation.Classification.SegmentTensorStabilizerStatement` | `13d1b8d7b9c4005a61eee41790794e51823e349ff7830aeb306b11fd817c3503` | `ec9a58e8d98f13b28972d974ac9384612d6c64e53c6852d6aef14c92e720656c` |
| `Representation.Classification.SegmentZelevinskyConstituentExistenceProof` | `e4ac2f9b66c118ddb660a7e13517e57e919e0381f4ab00eb9d55f2b13ef7194d` | `9963bc36b2161698864488a6ad3389562bd66561d469ced1227d307dbae72e88` |
| `Representation.Classification.Segments` | `b09e9fdc1445e6fabe2a923a896c5f0f5675fe31fd0f8adc7fe351e98346edda` | `ba5682b3f3e143817d63133383fc3b05469cc48f05ed20c9aaee5344b272189f` |
| `Representation.Classification.SingletonSegmentSocle` | `70f02e2f5d1edfda9a31beb6f1df8c068d786ab67ae8b908602ab554d929eb68` | `87318b6dd7bd992f408c4b82a79dda325263797beddb4b2096c724a6b1f3e43e` |
| `Representation.Classification.StrongConstituentExtremaProof` | `eae9776e3799623b967e1ce1ec3abacc38af9f5fb698c83ae1fc8c23443b5719` | `9e5641440b89fe83601555038d46e63e731369842b0123f214db8669db2354b5` |
| `Representation.Classification.StrongConstituentExtremaStatement` | `312c9497314349684958306e57ff24833ec7c37decafd6d2a237028472db7ba6` | `9ddf9150b5b8c51215c96b3ba539d3162485c06497e4ee9fa75b2a4ce97de4d8` |
| `Representation.Classification.StrongIndecomposability` | `eaa3b4ca45a4dcd30b3e78cbe9fbaa66ed8aaf6e7a25426661057ec17c1bf22f` | `47c02d8dbe8aeb9af7453d1636b18a0f3353978cdb555737645abd696bcfc8b5` |
| `Representation.Classification.StrongIndecomposabilityLatticeTransferProof` | `f7ecd406b2eed74c132c086e20dfcf10f9202989f752877079702689043823eb` | `9c5512e9e1e6e77d7f82c43b6473088913d15ce6c44cd4af3d2e45c6fa956c1c` |
| `Representation.Classification.StrongIndecomposabilityLatticeTransferStatement` | `5bb53a719805aea244345a4bf8483e11542493c8a66b31db32b6cb1fc8fbbbc3` | `a4fffc00bbb561ca17341b9d1434491aba31d2ea388760fbde7e410f41ee64dd` |
| `Representation.Classification.StrongIndecomposabilitySocleProof` | `452481d9bb0287d3356f1a93e7025cb49e20ab7519d3dcfcb54f38e1ef79af8e` | `acd83fd7a4452def43a7edce070f0ec0968ebfee2511b312bb48b06239f99c20` |
| `Representation.Classification.StrongIndecomposabilitySocleStatement` | `4d03e07f525bea4d9645a0fd49aa7229eac76fd18a059942a09fd9121e2f1a9a` | `1d48c2ee903a381181a552bed7f389dea22208b29699321557fc3c7665459fbb` |
| `Representation.Classification.Supercuspidal` | `c13ba8ffad11de2c3b2861c4afc385be2663b3e76963d5e89807ba92c753f9f1` | `b46be626d8b287d7011f47c8ee66cc8e22620efb6a94c0086486d75ee212f09d` |
| `Representation.Classification.SupercuspidalContragredient` | `ea687de5cec50b4eb5ec8e7eae865bd74fafde991ca96a29a7e1e9c2b83c836c` | `ef37ce3f0ce60c5bab18f948c3215344cb122d67b60749e8a4a513dca83d8311` |
| `Representation.Classification.SupercuspidalContragredientAux` | `b073fcfb57858c9a80029ebb148aabf16597a953d75c04dfd8967652908e3713` | `4a75bb9194c2ae7d0bbb31a1cc2b1e1668b9ea28ea953faa683d361bc979ae29` |
| `Representation.Classification.SupercuspidalContragredientProof` | `11c8e1f8955405b0574a25d4a8289679d851a4cda1f69c302a943b495136681e` | `c8e64da609d38058644c20fa6bcd4550d8e1744168713eb182d63a91603fc7a3` |
| `Representation.Classification.SupercuspidalContragredientStatement` | `d56c904f48439794e34a4029152063a94a19a2bfa908f15102eeb023e7971177` | `3904bee0caf97f7b1b558369b985149ed3378d57fb362b99837ca966c0b6de2b` |
| `Representation.Classification.SupercuspidalDerivativeVanishing` | `e675cfb3f681ae7bb1407773f51fb57cacb24edb4b670a84df47ab6ea356c82b` | `3f9bd3e497b118c4c5d5f6eeab466316d5986b675358bcc63efccbf60d32c2e5` |
| `Representation.Classification.SupercuspidalDerivativesProof` | `856a8cd5007362a0d80289eb10f9ff0fce2ddb8d5560a3e03bf52939253d52ef` | `3f08a05d3c161474f3f03deba1f265d418fe4620236d9fd4313a99cdb6d735f3` |
| `Representation.Classification.SupercuspidalDerivativesStatement` | `d801855c619a2a3afc59af4242c7349b32fa5c94e1720aa33cad4efc224e8d50` | `667f91d9cf578797ea1ea52737b9053f41c75507402a4f6b3048aad77d3dce1f` |
| `Representation.Classification.SupercuspidalSupport` | `4680302c6b5ad320893b38e1787f11739aca615cc8f44b38021824423089990a` | `7f8064dc6500a598053a8dcbf6dfba8fdc1a6413b49ccb4cabc3267eae4e6e1f` |
| `Representation.Classification.SupercuspidalSupportStatement` | `74d4b6414bf6aa146f1b5d5936d388a6e552c2f8f8341f2da66615d3ec19364f` | `4612c57588b712324930b08abbcbc7e4df7d6913cae6718aa7de1f2c7a41b041` |
| `Representation.Classification.SupercuspidalSupportUniquenessProof` | `df379f7274755ac4365a84b57b41cbc61a7e9f8850e8fa320f273cb96256bafc` | `81040d86160d32fb4a83750a6ce515b6d4e5668932b852dd3d48ef7eb61d3e81` |
| `Representation.Classification.SupercuspidalTopDerivative` | `693b18b56c1728204082857e70904930c97abd5f112bcf8999fcf79d43226128` | `8f3378b227104d52aba14811d4e3072472cca87169681748f08e74554b226822` |
| `Representation.Classification.SupercuspidalTwist` | `057738fc8e7b1aeaee62186dec29b412049a22f15ac7f71ff7759eaea1bf2b58` | `f3ed69bf8418af1014b430c58193a8bce4797cd18e72673207d7f0164d695fa6` |
| `Representation.Classification.Tempered` | `bf5ab02e57596efcef8e888e005c2d2f553195504b4556dde55f70f3da41b4a3` | `891db3351f3c2f141b0e244e10720dd7b2b7b0f190473666027fa24ec73cee4f` |
| `Representation.Classification.TemperedBlockStatement` | `4ee2708e0b993d1354692206ef105448e0f72572d3bf47e8b76b7ddee781c8a4` | `ec9c746a6e2ac6ed878494c95942969aa6954c4999ead9b32ee0e162a68868bb` |
| `Representation.Classification.TemperedInductionStatement` | `119272506a480330549a4c10c12a3cc25cc10830488c852094d7705bc989db90` | `0dc2c3c5f4eda5e797389e7d39ee4a15e052a08d805a581bcc7b33faff1ee9ea` |
| `Representation.Classification.TemperedSupportStatement` | `b9bd252df661d89a93ddfbb154391e7370978a8d8e89ff03f272bf84820519b4` | `32047c7876072f552c9979e10fd8bcd8ad4224d1b32c2b7305081ac53424fdf0` |
| `Representation.Classification.TrivialGroupQuotient` | `41e3a5da3661d8167b154571e3597dfd4ace16637118925ff74e5173a7ad9b99` | `a0c96ac7d520c8178d4e80dc375c67788ef23cf4b8d141b5110f6c83c86f2c91` |
| `Representation.Classification.TwistedProductCharacterTwistProof` | `e8c29f007c5b4404e89d63fceb8d29a0b2e8f7c0585bbd31162efa51441e1839` | `8d15a0023e6ed460e133cf0bb6d23e339115059ef0e6ec3251f4917f165ed67d` |
| `Representation.Classification.TwoBlockExponentNonUnitarizabilityProof` | `c741682533076eee530718443d389e4406007e4f26184d40c8ff4702e355a977` | `b6e22fbbe5066f59c89af00d439d0a217abc84f628808f56e79d42c3fb36177e` |
| `Representation.Classification.TwoBlockExponentNonUnitarizabilityStatement` | `825c3e487e6d39bd26d7c6bea1ec753b34df8b0de50cd8aed0a16fda0e478d4c` | `23d7700eb1edeec991ffdccf604fe9b78ecd701485f09fea9f41803f810ff101` |
| `Representation.Classification.TwoSupercuspidalAdjacentJacquetProof` | `61f4d108ec9ed632137db172143ae2c678a268be8f29691952f528a2a5db099b` | `1d668e4db4f3849905ff83c92520b76c0a738afd77b54e50ade710522f9995e8` |
| `Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof` | `52ea55430c26d19570a5b194f7c30c5e0cdb5cee19693eb444071fdd5374062e` | `cc8824dbb3f5049aad1c5ab4aeb4d82dccbe572a5304774d2a42337b97ac8b9e` |
| `Representation.Classification.TwoSupercuspidalAdjacentReducibilityStatement` | `2fc0370c485f56969be5058a2b1e38067301d4f87972fa505eb45c48811f66cd` | `318837119b9d27ab54628aa9413a21e7a3c141a37009a47fe41bc2c03e162ad7` |
| `Representation.Classification.TwoSupercuspidalAdjacentStructure` | `4aa352f7e66cd42479f55e21bcf2cb1d006598c82d0c54a2108046616e9f821c` | `0819ee90c5f27298f27dc504a2e90b037ecaa4f81798208458fb308c37641e96` |
| `Representation.Classification.TwoSupercuspidalBinaryProductBridge` | `fb411970fd1b14648c751910c8dfc984d351bafc2ecf74e88c3a6010c65946b0` | `12db858442f0b5bc437b61f5c6ccf4409f4fb31d8abb74ac47629a8289c03e9a` |
| `Representation.Classification.TwoSupercuspidalDerivativeBridge` | `aa6cc8f9155be4b27f2cbf875bbc7c37cdd286396d9ac84e12293ee09465bc79` | `24533ebd92ef91d73d371f9d07959c1803b35db6de6a971bbdb094e85bdefb99` |
| `Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof` | `683a8e648b92c65f40fa823c46fba6a513d8af3bfe3290bcd83e0959fa32b98e` | `295235ec3c15263c0795d148f419d8f3e15035ac47fb9e51703d058aa5e8d43f` |
| `Representation.Classification.TwoSupercuspidalPartialDerivatives` | `7ac770e7e0f6f081b6872881f39f6244811f711fee66c7351d6099029fc74e81` | `05eec67e4786272b09b56c3de336727460d4119c0955cb9b8f3ef89b68e00b93` |
| `Representation.Classification.TwoSupercuspidalProductDualTwist` | `bc49ce88f1016047a4e0791d6d10f2d0674e35e0b3152c6533461782cf32ec4b` | `04c76c875a78cf4bd471aa9f2538033fcd331f723b625325d3bc9c7e6b8be044` |
| `Representation.Classification.TwoSupercuspidalProductStructureProof` | `abc1a681ae0630849f899a4716839faec8afb3706dbf155b0364de34b6e093c1` | `d14990fdc5afeca206207f04dc48694376ac0414b95a48756df591a6fa8de631` |
| `Representation.Classification.TwoSupercuspidalProductStructureStatement` | `16cef73a9c6d3a11d8fdd85a8a61c866b255c7dda467e0ab6544bb0d6b008af6` | `02f6924044e16d8476a7f9e8a211ccf1f996e43a9205f421c9a944f2d21b1d49` |
| `Representation.Classification.UnitaryGenericCompatibilityStatement` | `743b1379e5142b26f1e867aba13b12371a2ffcc2437d3ed994a8aa6b2b531063` | `77aa1a23f065e4bf98e0d6d529a01e407f5aaf5b702c4e7b19b33d5f20aaf758` |
| `Representation.Classification.UpperCuspidalJacquetMultiplicityProof` | `cbbd967e71957e75e14d6747a18f66ee183e21617bf6aa320eddd9f12ab66072` | `0744ae52ae8cef5ddbb588f84717b3597a21ce9ceb57d94a42006defd7cf49bf` |
| `Representation.Classification.UpperCuspidalJacquetMultiplicityStatement` | `f76d23a3e7ee4709bb0c64fb185b9591691508651406212229ac61a4e38c87da` | `a57bd3eaf46a2ec32b6329974d8b75a0675d49aa778a4d39fd4c13d76bb4206a` |
| `Representation.Classification.UpperJacquetSubrepresentationDetectionProof` | `eeb8997bfcd15e464f63276e23df7526901bb6c2bd1d49c8d54a750f144faebe` | `edd3d0a16c21109ca201fc3916d4c6d1312d596ae415082650ef04ab0231ac4f` |
| `Representation.Classification.UpperJacquetSubrepresentationDetectionStatement` | `9c3ad79e11c4c0658d2ca1e492de1bf13c4bf0d0ad573e20106e6be86449eb82` | `595be7b36e77fd008b701d88e144a123021152d7e64d900e41a0c45327989739` |
| `Representation.Compact.Definitions` | `afb77f4a622710d058d58b781ebabc38eb3cf5ccb008fb1c12dbb4817db05289` | `fa692bd5cba2ec7b62279d74b85164fbc2c96e16ec8d97afc3589dd0a959e01a` |
| `Representation.Compact.FiniteMean` | `799a159a6d19aa67f0b464d28f429b0ff798eb8c86f469880c529d5ad834b410` | `92d4643860f10fc65b575766c7777cfe4decfc20c739944a6484dc261983b73e` |
| `Representation.Compact.OrbitMeanTranslation` | `3114fecb332ad8b7c66f7c74d446119dd84ce0148492c56b650869b20fc8dda0` | `09994e5506efa3735542e8776230265cd9f98c5faaba8c7dacdd27c08ed67f41` |
| `Representation.Compact.ProjectionProof` | `689b92fac7e04b7ee2cb3dd4702653725a597997331ca62c6461ba7ef12fcc41` | `a2217b34bacd418614535068dcc858ae3d44ad3a0638be726fc8838499f8d5b2` |
| `Representation.Compact.ProjectionStatement` | `f0e69eeed6dcc35d12fdb78f554f85e5913355bfc4d2057bf658b5343eb2e45f` | `ab65518fa3a8fefc07ff69610b4332dae41c3a8e34406fb70c94e2dad863e94d` |
| `Representation.Compact.SurjectivityProof` | `d1a89efb911951f85a1a691f4f5da3e76101f949eafae0d28b4e193e2fc5a20b` | `5c2ab76bcc362821fcb7363e69e752a0534f043779fe0a415ffbee792fad90f4` |
| `Representation.Compact.SurjectivityStatement` | `ad704b0a5522cf5c27f265d3777de04994e251cdcffdbd9faea69fc40ba54778` | `e1fc904da47b1c1b35a7104a1f27d3e8614a5768d346bf6b22cef31545d608ce` |
| `Representation.CompactCoefficient.AdmissibleComplement` | `c0198ac9e4f1d481afaf2358f478d01e88c0d9a43a26c77e84bfe9c39002d72a` | `612440124be18f662c7ec74ecdc76ea5b8aef71c1a0fdc4b688a31dc460421c1` |
| `Representation.CompactCoefficient.AdmissibleLifting` | `42fe291c7f75b9012d3e972f731d0f0a9b84a907f0617adab1281e38a032c2a5` | `3073e93056f769075b472d4f7692392c6155bc8b654ffd0878d55301aaf798dc` |
| `Representation.CompactCoefficient.AdmissibleRetraction` | `36621085e71ed8a1880e86067962595511deed94880ab34c9a91ec429b4cbd97` | `5264b138a2f1bef57fec90e75e87b70d4e16c4a70ab211e23fdcf769e0a3f608` |
| `Representation.CompactCoefficient.AmbientProjector` | `44455152d6b8e178e3cc600ee069eabf05c8bf25fc722659b4199fbb51b001e2` | `4ba98262cc078dcc580a2b9255778fae111e2c863eb522a187c23646f19dcd07` |
| `Representation.CompactCoefficient.Classes` | `f7a98e323a2a751b93ec052e64907c7e4674bc8f960abba1c89badf05023020b` | `89133c00c3294ce3418b45c203e97875d0fd04cd1e9ef0c6fc28340359e1d6ee` |
| `Representation.CompactCoefficient.ConditionalProjection` | `6501fec5180d09f665b1709591ad327f4197e2621adba7299f7459d5769c1967` | `be637f8a6b88175d4eb5f9246f5fda818722fb6063b0269c8239e554c0dd0cf7` |
| `Representation.CompactCoefficient.FixedLevelFiniteness` | `67ffc501f0051fed29269b7883bd1466fc4eb7e026d4b036745a410513022b7b` | `3d5f6b976cd913599ff2e3a198e22ceacb601ad0fe871d69d983da24cfe5dc03` |
| `Representation.CompactCoefficient.FixedVectorsFiniteDimensional` | `638fd3967a1a2e08ccc4382946891a88d570a8d1856f5dfea2b130592c91afb7` | `09c4533eb8cf5070293c97dd70a84099537b611adb43e9fdf0b03739f548e495` |
| `Representation.CompactCoefficient.GroupTransport` | `5e54ae1adb8a14e6f7bb2ae36f2d621b03e9af9e5bd45b92eff1eec6f5584423` | `ffb1fa1de95cd1aecd6cbca27dd2c04beda4255a030f800e5b446abea7278875` |
| `Representation.CompactCoefficient.Isotypic` | `c99e996bc8d74c1c61d886414bc01cec79174792ba097711ecdf01f6a6e7ae09` | `bc586ad6bd7e233d4ca1af3c2d8ea6c52e7f7c1af05d2b957834a53e499f7282` |
| `Representation.CompactCoefficient.IsotypicTransport` | `9043b81f8f887b6e1744de5454f5f15da24f8b18771dfee1cc8e51b73b8286ea` | `1bc01b2e5fe7961cc5931d158cc9e86ab9ee455e09d51b11f4a667ec1f27a47f` |
| `Representation.CompactCoefficient.NormalSubgroupDecomposition` | `da4b0094ec108cd5e76f3fea38a3ceadebe448a91d9fe38cc18a554e232b1cb5` | `8f32243a35c3ff6ccd179a786a0acff8347137c4d1193aa3c88f1c99e48644fc` |
| `Representation.CompactCoefficient.OrthogonalProjectorFamily` | `7819f4ca72095a3c36bdaaa310206ce1acbfaeb54f45974817ce95bfd17a995d` | `19bf5730aa6500fb2548dd3fbc18139fb7db13fce19aa3f701720d7576a9e110` |
| `Representation.CompactCoefficient.SelectedAssembly` | `d1f75fee0640ef72268e63a4aa9096dc82def33aef5b375a1851fb10b63ab1df` | `79b53ff06455234e4c4983b60c5cf215c51274c1997e52fab41eaa22a31624d4` |
| `Representation.CompactCoefficient.SelectedBlock` | `53cbb129fc96e942074670e12c9a6955435cd02248ca0b27fc1b157883871ad0` | `8101ea8fd3b3b0f5d2b89d95853e6ced09ab376711b54ad9be2e30b58eb2c300` |
| `Representation.CompactCoefficient.SelectedConjugation` | `6010adf76a910a67387e124f0586ca3dc66e959b2704dfd927c46403a99c9eff` | `932fc29ac6671e25a8b5ece25a5982f4cd1cf91ec9f047913c15a1c2a32850de` |
| `Representation.CompactCoefficient.SelectedCoverage` | `73441b56d3257c5561704ef5a364c91b9448ac7f428e5ed622ab95ef0825e003` | `ac5d6f844681f9f0ea46402e752a7b0538fa006ea911e7cc0f209071ecb043d8` |
| `Representation.CompactCoefficient.SelectedProjector` | `738b02ba15c21a9dcbeadc8a30bd36a454452b64fc281c676843b803deb51bcc` | `6ad71fedf3a3cec80dec2d382fe6a000de0cba401dbf90ee3e414e65087a68d7` |
| `Representation.CompactCoefficient.SemisimplicityProof` | `2343278f519584ca43fc8dfc38263f31c738b4317b834a79cc2f8e85c018d642` | `bb0a3a6698be7129964c8ae1c45d81c787091adcbecd209bcb9269efcb8c46f9` |
| `Representation.CompactCoefficient.SemisimplicityStatement` | `8e9f7ff68c7a2d61193f5f08891fb818f4985955ee680c83cc1421b4554a0389` | `ddd9132288f52ad3186fca3d3de164bc913d56021bfd8222117d9350622c6a70` |
| `Representation.CompactCoefficient.TotalCompactness` | `ea96b95381ce42addecafbf34f5e4dc30e5307148519ffb88bcaba18d858203c` | `d5abfaceb4cc727c1f7d0fbbbda2085862bdcbb214d711ddb7085957816ed960` |
| `Representation.CompactCoefficient.TotalProjector` | `5238f0e26d7b6f0716c95772ce48f72a0f2758e44f97fac7f3668664f8f078d8` | `320b152445b5f9f1c1babb53173fed8eba2a36f6a68ff358da216764eca1ab94` |
| `Representation.Conductor.Congruence` | `c21658d4ae14ca5740227ec1a8c18bb92f44a5bad437f6e98a665de4c9e28b70` | `8aa328c233e7dfdf26ec843000690a66d56548686e83a921bb414edd567582c6` |
| `Representation.Conductor.Definitions` | `1e1344124c2d1332d01130297405e48e776bc74eaae7538221418521dfc7e0d8` | `16d689abbf922f4e26bee7d1d49fc40c5d36822cc3327c6c1f82c1b7995dd083` |
| `Representation.Conductor.PrincipalCongruence` | `58b5a6df788c0c5ab2dd19144987459fd34580149cc88c9294f08a34c8df39f8` | `34cd70ceade46dc39afa100d5daaa7f69664ba8a8832494a6a9d4f6a0c9202db` |
| `Representation.Conductor.PrincipalCongruenceBasisProof` | `dd76052e5d498a6139db7a053c8e0e3326981c1ac66cfa6fe46fb91388fedeb8` | `fd4479f22e5fa014448001bed936d6c3f6ced370b39c46a77069d86476ffd6c4` |
| `Representation.Conductor.PrincipalCongruenceBasisStatement` | `7d5d11e2da5303a626e784c7d6591874334db491b0d533335556c10025e59b9a` | `6be5e8a7896363cc631c9ab8505eac3832650a3cfbacfd68bf383d9ae0b5037d` |
| `Representation.CuspidalSupport.AssociatedAssembly` | `fc9f750f0fca2f81e2d1dd0cfdb3c0539ea16ff0d8bb27d8069a0961255b4c3c` | `f13c974ca5f51ce532c1186c0391ca261605af8b1788379d6978ae6d2ce060e6` |
| `Representation.CuspidalSupport.AssociatedConditional` | `0c596e38b4748c5b2577ced7129b7ea122f8e46c34a813834d032281952a29e2` | `c5d38e78cb38b6e6290e115599f063fe93cf1ed3e4e685117098c575744a7a77` |
| `Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof` | `42b8b934042767f834a92723f3320c4c056b5aebd46266520843e7fe53487ada` | `56efb4e5e23e14a26c25f82aeb8e6bc975fc4ea7b19c198e5545540bcc047c60` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` | `081e628ad507b075157ffefdf760e72e3e38fa5846d256989527fe5dd8dfb579` | `c3de902536f6d1f915245ee419004b3bdb5348d5a62022987f5bda596176152c` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesProof` | `479dc76d7e975b9cb504c502a8547a5f38960c7950525950d80db93eb2cccdac` | `9728fb57086fce627ebd8eaa4b32301e8b0cdd7a5c1386e0f5f2b39c7cd8c26b` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesStatement` | `fdc8eab0692b8be45c8310f7b5cd3670f1bb66b45212d9d3be17b4832f9be714` | `d5abf7313e1c542dad9a5185171910c6329815e80261a900b09437849c5f4051` |
| `Representation.CuspidalSupport.AssociatedProof` | `f5b549ee3957da1ca99fddc6957235281da6872a5c746ae6d6f081af8ec509f2` | `c27af1a5440e9a51acb2be4e862d1c540ce66b80acfd0a049e48a46279f7a7b9` |
| `Representation.CuspidalSupport.AssociatedRankZero` | `58c86f8df1fca62f1a23ad201fbd7aeafbe1c52966c8dfd6f7944cda910c759d` | `f26deed5d9b7e0e3221e6a2b2b6696c0037cdbac16c73be9aff0db437afdc311` |
| `Representation.CuspidalSupport.AssociationForwardHomProof` | `c6e2d3a7ffde82aba157579ba6f1883b912359b25cd954a27521e30b60a109ac` | `b2cdd5ad761054494984654aea03de58f7ca0a7e0e792b17d894ef1a6d0aaadc` |
| `Representation.CuspidalSupport.AssociationForwardHomSupport` | `1645560680c0deb482f4f10e6cf17b6f3bf081e93b5366b8d9bb5d798f4f10c7` | `ae55215d541d69cc4f702809aec630aeb493bc9488a3b7f44a881ac7ac925d09` |
| `Representation.CuspidalSupport.AssociationForwardStatement` | `b1de1c921773498d13fc899285c3dcc0409f60a90b71bb21bfe5ed758954d811` | `6cecd216418d4ec74177c84e998fcc76c26082ca0b5da43f70cee98d7dfd5c52` |
| `Representation.CuspidalSupport.AssociationLawsProof` | `3020c3048a16551901f6a866496fbff39a7ccfb2b611b5312d898ef136a15b09` | `e2b12a7e0a8383d8c3358b4e4f52faaea41f75451458f485b239ab259de3786d` |
| `Representation.CuspidalSupport.AssociationLawsStatement` | `3d2d2f347c1d0e0014d00f526432da9f074e52b848520e620af1404837df94fc` | `825cc79589892076663984dd293f2fd11fc686503b9e67be7a3855e0806e007b` |
| `Representation.CuspidalSupport.AssociationReduction` | `e9749ae95762810af9a6f7b9266160a33d20e24b3f02d9b9959b14f62c188788` | `24f8ce626bf6262efa1e7250f5ce268b9d4e96003e32f87b68d630ea9d04cdff` |
| `Representation.CuspidalSupport.AssociationReverseProof` | `c4b506818b3f2fe5c78d04540ab637aa45e7bf683ff2896724b6a8b015129be5` | `f8fb6ce19e892cfcc54811f39e31c31efefc10a73a805cfb595284ab6aec57ba` |
| `Representation.CuspidalSupport.AssociationReverseStatement` | `dcd81e94fe7ead2526fe5225cdb95696f1ec7d4332ef2df536a45a9670311670` | `876c1cdad04196a0042c1cd40eeefaf95887232786030643c19b0660a8a8e5a8` |
| `Representation.CuspidalSupport.BlockMap` | `ee4678c80de8df6bcec60b366febab9bd268de6ad145cef0bc8a923b8576ff9e` | `ec81e19b491636e87b1d6aa5ec01a800c5235b6f8d392d7b7e643371a49a09d3` |
| `Representation.CuspidalSupport.BlockPermutation` | `550986fc9c16b8633729d4f1ed038813f94621b0dd32a4f9f32c4f0aa0c0084d` | `2ae62890d5c1bfb381abddbb5853cfd9f64cbdf47a55c09b82c6ee9ae04a9a21` |
| `Representation.CuspidalSupport.BlockPermutationTensor` | `8aaf9c45900e6da05c0c2f4e432d4dc38709a7fcef45805a0aa9e5425986df72` | `4a4b3e408b2d9e36ec618cc7e2b9c0d21d75467ced08d29901d4a1d34df94892` |
| `Representation.CuspidalSupport.BlockWeylTransport` | `987bd6bf7b90d5de3ef17db23f4c277885c7018f798680b1ba470342f53e5435` | `f94db0e672fc166cc7f150c958a4adee9bc791ef4def7936f4fbb6dd0205cb2e` |
| `Representation.CuspidalSupport.CentralShift` | `a9e4f9e0c5e3068a82b005f414bfcbed7e902e90fab340bca36e207dd98c8ffb` | `6b17c3c257c1ddce837461aa866141d6d4e2852abf285b5e19b825a060c1ba80` |
| `Representation.CuspidalSupport.CompactCoefficientFinitenessProof` | `396c78db73dc4019debb78d3ae196e8c38981df4cc1933eadc24816da595a129` | `b27ada7b75e0599b28bf0a4a6d1336fb835884ee484cc82978c4aad47d0c4abc` |
| `Representation.CuspidalSupport.CompactCoefficientFinitenessReduction` | `481a5e2dbf3536b4bf705a3f04059934635ce6495d98071ca2b580a24a9c0b53` | `b05e0b9cef0d6e33307ced4c5b9b6b2057691149e2d9ff2ee856150e225a9aab` |
| `Representation.CuspidalSupport.CompactCoefficientFinitenessStatement` | `14785816f50fe23b6fb7ade5e4969222161fbe48d18b6699808e406eaa34aad2` | `57c218a0bade5b5574a9a0219c78bab43726474fe6180bc09f855c47ea3e4de6` |
| `Representation.CuspidalSupport.ConstituentComplement` | `fcf54d25009dfe078dcf0ccdec739f6f0973c537adcfe80558c18c929e594ed8` | `616294897c0dde3b44fab353b9ed1de247498c25e42d8652847ee1665d7d0859` |
| `Representation.CuspidalSupport.ConstituentComplementStatement` | `6e85e45dcd85c32e66ee402ab7476b2f8eb26c8366fe50df27c24df704dd1be3` | `c66e78a3498d0ac3a376e0833d88be761678a71ab1ff9fd3fceb9e78b94aaf9f` |
| `Representation.CuspidalSupport.ConstituentFiniteTypes` | `dd2cc2ac5e3adaef0619676883d97e1b92d041fedc9c6137a2c0ac98d0666602` | `eb1c6279f70479adf450a51418cc1d82d3252ca375120c50f2938a948d63ee74` |
| `Representation.CuspidalSupport.ConstituentInduction` | `57a729e4e419c9f3c1b2f8317fe65434d8d255b54c05ca0f7b6f18e2192bffcc` | `7c590aeda138e2bae4a13ee57aaab059542b4f44853bfba1a386111a407b40b5` |
| `Representation.CuspidalSupport.ConstituentInductionStatement` | `2749eef46d2fd9a6615f8e824e5983126331d0532568286ce7513dcf0983991b` | `eaae44c16453deb0cc97f015b28dfd9e10114a5dcbd28f0a4d89632d2613f65e` |
| `Representation.CuspidalSupport.ConstituentProof` | `bc8a1b6b1356b7b6330441987a47fa222206d50e476107bc40aa99f0f6fcd2a8` | `19fca8dc6250b24e58bf774f5fef58374845ed58cc35cbc29d8cebc2d2aaefb2` |
| `Representation.CuspidalSupport.ConstituentRankZero` | `c874ad1068ab17f04ac861eabef9290f0b7ff9107f9dac5948868fa8a5b050b2` | `29a6a948903a3e1787565e9743cd8cf6b1bcaf53aeaab444660feaa639449e74` |
| `Representation.CuspidalSupport.ConstituentSemisimple` | `a8c1fd22e1520b0647dfdc6c52048d2942ab3f1585733e3cdc04537b279be46a` | `b747952f77079f39b98709abbb7ce49036e694814fffaa4b19ec6d03e3bfe65b` |
| `Representation.CuspidalSupport.ConstituentSemisimpleStatement` | `b76b00b37926c451f8ea720ce3c00fd514ac85a123e723fb70e4ed87534886d9` | `9aaa7dd80c3dc532e583e97a3e01f1ffc48c479f97dbb8de6f2e7e70ee9536a9` |
| `Representation.CuspidalSupport.CuspidalBlockIsolationProof` | `de4693cbdba066c3034b0f25e8a754c0fc48bbe80eba4101151c927ad44cf2f6` | `e794a7ca53d81bb134d8da7463188a92526f84aec32e35780f1a0e8c984288da` |
| `Representation.CuspidalSupport.CuspidalBlockIsolationStatement` | `93b8f804a2a26df47a1966e7a6518fab1fc39e30ea13260df6710178ed230690` | `f0cccef60a929b16962d1816929c54cb992d3d959ef54f88e6d22d22caf508f4` |
| `Representation.CuspidalSupport.CuspidalEmbeddingProof` | `a6a2ab87036ca4e6dddd785fbfc818127dbed5093db0714e935352605aa5f051` | `5844e55a1dc3bc8648682d1773de68a0c266325be926b757f317c378f20f4c70` |
| `Representation.CuspidalSupport.CuspidalTensorAssociationProof` | `fc2f5dbe34edcb7e9b8dae6aceac3110cc11d0c40509c188fc28908eb3dbc0c8` | `81c929c74d1402ece6cce5e90e66889514a88ad4b18d0fa5b31d32709de11f27` |
| `Representation.CuspidalSupport.CuspidalTensorProof` | `beb47ce72aa9eaf5f254092cb77463eac3d98688855073df0289796459f6197c` | `92a8ea63a408b8bd4124eeb6e93179ff680f10b4aab138ce704b0002365d80a8` |
| `Representation.CuspidalSupport.CuspidalTensorStatement` | `3670f5fa0326d0cbe9f4e0c22ced2c2edf6a73dd9371c797759c64f85cbb0e92` | `4a4381e657dd7f0f988407b113e9a41327807e25fbc4315ef1337eac0835d6ad` |
| `Representation.CuspidalSupport.CuspidalityComparisonProof` | `04d1e6e0cfb2201265145b08d642c48627183805c13ae91e098f4f2938c5783c` | `96e3dbbb6e5b63494b08718745c93b2a06fff9074b41ffe20a0baf9ff4e2aac3` |
| `Representation.CuspidalSupport.CuspidalityComparisonStatement` | `6eebcb9f841fcccdfafae53d677c5381f5d96724b5412f132913dddf3e2e2a24` | `cc5b60bbf12e42fba30589ab3d6c8f11ce2115be46397a385d3a2c73a43a7324` |
| `Representation.CuspidalSupport.DeterminantUnit` | `5d9df5617d7e1bc403ac9a271e1ff0a987cf156f03f708f5eddc4fbb2c699a2f` | `c87adf252b788bc08338c987f00f38e8d72d22e3490aec9c9cfea75c4ae883c9` |
| `Representation.CuspidalSupport.DeterminantUnitCartanSupport` | `968cdf9221e31c77bb9e6de4f6ec4925c93e6e324509108b79f8040cd1fa4333` | `c2ac4b2969cbf62171c7d478e9909994c80c441f13a41993363313af37acd0f2` |
| `Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof` | `191273fda24a53175b24cf2aced59bffa5d0139e5c6d512270cbe0d6ee7729e0` | `93f4625c7bd3b48e13f2430e109b97377526ae0fc33243f5fde8b89ef9a80efe` |
| `Representation.CuspidalSupport.DeterminantUnitCentralCompactnessStatement` | `655769e78bbc3448d10527af0a030b6bcd060a57eba08bc46fe929b87a3b0966` | `81002b55cd0cea9298f37e8c71aa8dfc982cd987033613ec5eac40e9e6221747` |
| `Representation.CuspidalSupport.DeterminantUnitCornerStructureProof` | `be0eee513292f54f186d2fdc282c8c6b5a684e5f75e4fec473332af6bb4b4d76` | `213798fd625ecc19b7e8d0799066eefb9dcb4a039dbcbdd516f4dd6b006fcdd5` |
| `Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement` | `e6537bede622f25ff6b70b93fee04e1d4473c44f8ff34e55606834342f63b6a1` | `11a2462882fac31c7b2134cb2a3b3c6b45e7751cb52dc01f8bb30b6aa79c9ff0` |
| `Representation.CuspidalSupport.DeterminantUnitFiniteRestriction` | `f165b520c82027b696b1a46e16a727d19d675613d7d4b5bf506b39f0e1ef5ca5` | `a99628a92752cb11bfd6222c2457cf249ffcb1f555497a9d9ffd0bb51834acf6` |
| `Representation.CuspidalSupport.DeterminantUnitStructureProof` | `62517aa934ad368afa7ddfa3349e1b27673ff85d15747cf511188495f8913691` | `1476bdf39cd280f4c82ad76053fe51e27e8bccaf992e9bb932f7db7eba5f59fa` |
| `Representation.CuspidalSupport.DeterminantUnitStructureStatement` | `5f3e89f083cbbfb1d19d8011eab30a2683ab575019fe9a815c2af951f61fd5bb` | `b5ea9e0c1e637c7ab5950d6d2cdd2eda41874aa14548db9bbd11013cff6e6121` |
| `Representation.CuspidalSupport.DistinctTensorStabilizerProof` | `65b370214fc0c47c321c765f7f65dd454a55e394818ed1d0116cd45c58a792c4` | `08e3a63f413df114a6019757c5b72932ba7c4174db796f50428d6ea5cfdac551` |
| `Representation.CuspidalSupport.DistinctTensorStabilizerStatement` | `0c5f0642b0208f986fb4a38c5eb1349512ffb6f67b264324e9c4dab547cd826d` | `92e42437823738b63ed6761c846e57a706afac62bd486c21a55615ff3c4634af` |
| `Representation.CuspidalSupport.DualAveraging` | `3ac8fc416088496ced4913c119d3c5f407c8c44b4161febdefe98f5599e8bbe9` | `44f9d94d290b70e94185c08771cca251dc2e56982809bbccc0ccec50b24b5cd4` |
| `Representation.CuspidalSupport.FiltrationQuasicuspidality` | `62654fd06f826703ea7b9149f56ec41ae1c289169a6e5cb2d6ecadf0d80da9f9` | `d9c64b96ee7be22313c5f3c34df6ffea2036646bd28747292194943c46b94ce0` |
| `Representation.CuspidalSupport.FiniteBlockShapes` | `95a048178cdec1f8b1bf1b79cf7238322d23622022a26b610cbefb31e4b40ff5` | `141fce08a749aa5fc8e88d763c14562520084655a860f6dfa4a7d63c3ead4d3c` |
| `Representation.CuspidalSupport.GroupTransport` | `9ed63f8d70d23a9bb07a44f063ede8ff4f8c688ff9fb8d90ad110678c084a28b` | `9ec28e8ae51b14bb99442cddbfe3db1c041ebcc7d2ee8f0e052bce69c8601193` |
| `Representation.CuspidalSupport.HarishChandraAssembly` | `a48219f61bcf1a6a5ec77b0e6430c48462fb105bf5d30b92c2b150ec798452e1` | `a84587aaf350f1680490b94cc3cf781ec8ca578ef6bfa41880ccd6b6e31f8595` |
| `Representation.CuspidalSupport.HarishChandraBoundaryProof` | `a4fc867d7fb003e314ef77736dd0ceb090ba1e65abfe838c4f6f346ce1be6cdd` | `0d7bb038ef9944be6a90e4c394e7edcd3c3f2a43121128524ec2ff6f0d03e7a9` |
| `Representation.CuspidalSupport.HarishChandraBoundaryStatement` | `aa7f0e798b5953d40e6886fcbf7e6cfbb12c7a82d19a0dad5c501339a2c42004` | `b03548ae847c2ef16d9f7b16d9b26ef3b24074ccba142b973629bd2f0c9ef485` |
| `Representation.CuspidalSupport.HarishChandraConverseProof` | `9c7bdcba6152102ccb9dd3b5166cfb514a8af43d09da32b8b44f02d1a5dd9bb6` | `8671c00bc800e2fa2626a082cda8ac29481399cb87980718ffc681f457b3c006` |
| `Representation.CuspidalSupport.HarishChandraConverseStatement` | `4ed9b80bb1027ccbfe39fc5e8d69f0447f5a3b29ed515ec9e4996e4064be9ea1` | `b2490e0de004a857012475119dfe2957ffc9dd4cc35f9c1c7ed673f43726e9ac` |
| `Representation.CuspidalSupport.HarishChandraForwardProof` | `5f7edaaa6c364d3d6da9014a2c71310aa966705b78ca0b8922195ace88d46b40` | `a2c9086f9b68b5a91327ed7644daa4506f4a40052994694ef18b60a3df1269bd` |
| `Representation.CuspidalSupport.HarishChandraStatement` | `556310c1c30731c178b5c13b8e9cc0ce97c70e072f02863d4ed08657fcf4210b` | `3f7746e518efd755e93984fb60dda7a2de0cce2cd89224e9315c67c76a83e261` |
| `Representation.CuspidalSupport.InducedJacquetCount` | `0f1612df05dbe49a9a0478f5c75e4cb432d1fddf8d933a53233395aa26b91d98` | `a899e55ae6650ca51d9ddc85f0f0e0ef7e8c47c52e9b1fddb0d52f0088bcaaf1` |
| `Representation.CuspidalSupport.InducedJacquetEvaluation` | `c2dc16a129bc578b065e4e23dc5c1dd076bdb87cf26f90663260a0193811782b` | `e6a288cd773e41c40728c2bb03788f519359fb30d6fab51dd05c95ed74dfcbe3` |
| `Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof` | `ba098664f9c072345999f38ff8e38c8715b02386f0cce0e42f67efc275ccae2b` | `1d0ed37ec0f392e04ea8447ddce9d187222066b2466a8b52f24afe1ff2b5b808` |
| `Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement` | `3bd72a06afe782cef813ad2a4ef95bf6de69e29697a4b2b6bc5f5401584fdeb4` | `63699f3b1e7769609136775e49889c8a4d8617de70160f9746069a3b21c3b796` |
| `Representation.CuspidalSupport.JacquetInductionStatement` | `50b1bb4130a051c6220b65b4528302db3dfd49443e35349637c70145ce05ca7f` | `c81abe8cd83d1e27899a073c32a6015c1637b289211fd67b7049f70c9241d7e3` |
| `Representation.CuspidalSupport.JacquetLengthDetector` | `31ef37dc59d905947ce526d7dd6fd8ea04434fb73f520a93dba63bf4ec73d0e1` | `6c1a241c3c72e6c0fc0f7e592d90b0cb08f5b50349fdaaf2a0df4b72580f370c` |
| `Representation.CuspidalSupport.JacquetSubquotientProof` | `32894a8c88ede5843e36786b8cf5367797ecc0c758de0fc2853b55657bea533f` | `62d6136c7f445d55a6954933a507dec2c13c855bc3fbb012b9064a064e5779db` |
| `Representation.CuspidalSupport.JacquetSubquotientStatement` | `ca79187f11ecf97d1ae4d0e238a89f87e63b00e73ce34b1f99fc9a2fd67e0e8e` | `6a0efd51d5b5f5000e7949652b54f8a5b12275b6d8c1efc30bcc12b1420addc9` |
| `Representation.CuspidalSupport.JacquetVanishingHelpers` | `8b6dd3584a21a8774d6c4a42b18710d358c025ffa5a33088b0c04356ff4f2303` | `9f34a890350a837c4a58c35118201adabf2a9e22203104bb18bc8c151e614d8f` |
| `Representation.CuspidalSupport.JacquetVanishingSmoothPieces` | `d9b24c6c4c9988eaf5ccdb3c73ef7d392cd77e2ca0fc3f3127ea037053a1c33f` | `25a933e1598ffb67b44fe891ccd5ea8f0c54c73f62627a26ef277aa47c54b547` |
| `Representation.CuspidalSupport.JacquetVanishingSubgroups` | `342efc111293e9093fdde1e324f05ea98300874a5c425ab6c91adee09bad858e` | `ed4ca879914e554fbace2ab5166fe3cbc5b23ed912b8ee36de9ac3858eb338d8` |
| `Representation.CuspidalSupport.LeviAdmissibleFactorizationProof` | `ac88944c4e74a363b316bcdb3f70a5bf69f081e1c92bb3088d632029a3f53ac3` | `2296000b564fe9eb781f3e863cffa9137868b42373c6d1d67117c65ed10325c1` |
| `Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement` | `f1489326737d0cbc5930992490f2acba3e28013dc0da1106b5e27e579dbf0867` | `9b575b15486e19e351a66f325563489328ebf68d9c08241ee6e5e10e198144db` |
| `Representation.CuspidalSupport.LeviAssociation` | `d12750f064b37c605b27952a15dd91f92e5568d75f7de89bb30a6eb0e9f05630` | `6cbf1368ec44763c91e31f09b18d711e80e9dcaf8e7dc44cd3734cfa0219ddf9` |
| `Representation.CuspidalSupport.LeviCompactPart` | `a3f8febb21f115628dac6b4f07c294ef09f2dbe26fc2a479ce3950d4915ae071` | `fc1f10caecd9f35bcc9f0d8db98b45fd507c8407d89aba22b71f1d6573a59562` |
| `Representation.CuspidalSupport.LeviDecompositionAssembly` | `0ffa7873096c3606ae60f8cdbf8d09ed1175633c1d0f8eec47601cbd8053dd86` | `ac9175876a017c7b3a205626073545df9d94d1c14ee4d8844b62d07ddd9b9759` |
| `Representation.CuspidalSupport.LeviDefinitions` | `313ab39ddedd66f91c734a1e8b9fdae6a8e4eebfb111e464421c28cbef9aae38` | `ecd6d283a17bd6e81bca58d1f7f61628fb5c501be5f1da955f435e324d7a12a2` |
| `Representation.CuspidalSupport.LeviGapVanishing` | `0a9ad59eb65018ff8a575c253bd70f908fcfb1cce315a07b42db67aea7fba491` | `cb5aceaf23675821eaec59a9793d3fe000a672a4ac5a584dea1f43a38bc69088` |
| `Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof` | `988b5f33d8f1301117ee250b2716d744cef521d4f72f6db32ae8fdebabad74a9` | `173516b1ca858716d129c34e71cc3c325396c2f8366d074f5910a097861dd38a` |
| `Representation.CuspidalSupport.LeviSplitContraction` | `d7e1117f7f901a2afcb6a7fe9ec0f6a03647cfdf822a4c1a1dea70038f463b77` | `3a682aa4410685a7cf32d68c18f6f080b8ffcef6e3e13419ef0efcad6566ca8d` |
| `Representation.CuspidalSupport.LeviTensorFactorizationProof` | `02071f71e77610aa35d3f97aaca838f9a3f7e4d4534f062f4fc009f465cdd958` | `de78c9d4b2f62d5111702f8d34911e5970c9088befeed014c067971403201b7b` |
| `Representation.CuspidalSupport.LeviTensorFactorizationStatement` | `39e7efdf6a13aafa747882e2947535ab8da0568fdc10c928e89dfc211bb7118a` | `339a46a357b532c67632fb509b9305a381eb77f8be2c37e74476e4d801fd0c46` |
| `Representation.CuspidalSupport.LeviTensorReflectionProof` | `3c4d6187fd0521170ea33ef3a452a5102f4a123494e112d59fd9128a9686434c` | `6b73e99a04ea3a89708bc88ee956636dad89fb69dbb3a76780e547c4d2f30b37` |
| `Representation.CuspidalSupport.LeviTensorReflectionStatement` | `d2546554416962f772045dc5048fa5273969afd1d0a826130fe856afee7f8fee` | `d8c37f98b97f262835340d7f05476e578e6136bbc07d9ffdb3d607e26a719ce0` |
| `Representation.CuspidalSupport.MinimalConjugatingCosetsProof` | `1af7ebce50dfdd200bbd00c34a399ce5479e41be34e674119b4a95f83c42c43b` | `4d88f5e21d371e61e17b3addc96d93480a3ca1ec4e12943cb339211d492e05fd` |
| `Representation.CuspidalSupport.MinimalJacquetProof` | `b54498cf8e6c63537c3e88517d8563bee112754c1671380da9b2afc99dd9c92b` | `dbf91aa314b3eca462e08043758b1b189f13cb210d1ae6d4b029c7ef8818db55` |
| `Representation.CuspidalSupport.MinimalJacquetStatement` | `a30a8476014772d600197ade10b04ffa6d9d0b3fe1d4a8fcc1a34a6d21844604` | `98a222629a5b55c1dfb7832fbefcf8712dd09ebba33bf0f7150daf5dabd093c0` |
| `Representation.CuspidalSupport.MinimalRefinedJacquetProof` | `5531fb425246fd31574acb12fac74d12d83203a4b486ca74ef48ee3e2e516cd5` | `ffc1db03d9ecff2df9b38b64089906042f82f7deecba91159e95b80ba0bc8700` |
| `Representation.CuspidalSupport.MinimalRefinedJacquetStatement` | `e3cd6c8626e4a38cd010baa0b69debd81258745e26cbbac319e1d957a9a4ad64` | `35f525274cdd2094e219cce914e556a2afa0cbab8a4d9a479d8eea94f8bc3c74` |
| `Representation.CuspidalSupport.MinimalWeylTransportProof` | `f92704738b48714c34bd48d08e3714904a3af97d4b964eb23021fab753619808` | `7bf2827f51608e2f72d8f1cf8db50e2873dbfb8230b4dfb5b20cfb6502b349af` |
| `Representation.CuspidalSupport.NaturalProjectorDecomposition` | `c401ab665ee5b86b86781ec0af6f62b3990cc09f4c8e68103218764fef0a0856` | `ee9c62443b3ae6366a473f3d43248f9daf7d15d11260f88113c12ca04d789ff7` |
| `Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof` | `beb4d2291651d39281be885f666e0a6b0c2b2ef1ff8b744f531cebaf9805be88` | `8ae24bf9e925cd7c01dfad78827251515eeb73f37bef556e4e9f92ea710a0588` |
| `Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof` | `ccc3d468f32040790389f1a81276e1eef5b0229f7a37c0e56e473a9eda87e489` | `7bfe229f84d4ad77d57c8421aa5d9616b59622ba13865abaee70c153a5e54cda` |
| `Representation.CuspidalSupport.NormalizedCuspidalInductionStatement` | `e702e01039359e8e328f3e113b642d2b3f7795bb555425414fddcd958a007a1e` | `9bf3bc29a9c5effa0ae07a501731a457a28fe24090d78a6257d1ad5c04a36269` |
| `Representation.CuspidalSupport.PointwiseProjectorSum` | `a1439565655bd3c742a1892873ac9a1c485c6b5784bae7d0d1595060f7145d27` | `cb733f188802bd3b072b64e49fbc704e49654af6e64135bad26898885fafe427` |
| `Representation.CuspidalSupport.ProperInductionMaps` | `86386ec00ea1de180cb9d6869709e327263a59ac94eddd8165bae6c9aee1b6de` | `4719d3d1872f04dcf8c9e75a6c9a9bfad9cc81ca960d1cd851e958e6bb8f3e9d` |
| `Representation.CuspidalSupport.ProperInductionProof` | `c90af9fa1838b66b88d82b2c5bedf7e2dd64ac170ea8a920e3eb69b736109cc8` | `e138c2688c6e77a6ec2fb4c5878ccc3fc18c8f952d44c8fd0a0653a75667fc25` |
| `Representation.CuspidalSupport.ProperInductionStatement` | `388467044929d0af465abdec5acaea2d6ff7362369966f45150910dbbc4d9691` | `1ea3f9a8c759d0237a80e5fe83ad7e35de2e1df4a3eebbf6f2e3379478f739c2` |
| `Representation.CuspidalSupport.QuasicuspidalEmbeddingProof` | `55dda346acfd733aaf8ef36e4f4b5a3d221ed7adaf43d465deddd114347c2c92` | `1abc8e25fb72551e3f1b61cd84d1c28e71f43e1cf17da4fb8adacfea3a3f57a8` |
| `Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` | `5f33040be3942c777f81baade7f3b66db82927564ebd3e536b8ce3739e581a0d` | `51632a041da31d50ecf64c5d07c119a1d9b911fe1a7be31b8d6a64e48b12dee0` |
| `Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement` | `c86cfb711506273b2023b084524fdc6c7c38aae9b7339283c2373099672c7dc6` | `5865473cbf5b6836d52657c2f5259da46316f0f6e575fece168481b1af41822c` |
| `Representation.CuspidalSupport.QuasicuspidalStructureStatement` | `7c7841d6081f80008ffe05b16bcb85d3e04e2526f0030d6350e57bf228940975` | `38bffee32a7794d86442f634d051161821f3ac34945f0b9e397adf95b36b013f` |
| `Representation.CuspidalSupport.RefinedJacquetLengthProof` | `3a59091bc575531c0771de744cdf449a055d34ea1e3779a90212bd142d2b4a21` | `87e15970d147eb7934be371fb838ac55f63af88544e6ad78999bfdd03864376b` |
| `Representation.CuspidalSupport.RefinedJacquetLengthStatement` | `de5be9c2c6be86c91462b5fb9b83405357a5b160627291a2da56857ae66aa882` | `f14155576bf7173147eb664e885600671c236b795dfbff321c064837f051ed49` |
| `Representation.CuspidalSupport.StandardJacquetComparisonProof` | `a5816b66578d0924d3fbd41a45ce445e88c596a84b78eaa02aeb1323314feee9` | `5f9a748c427202014b29dc1e6491b564166fd5a432ac8ea29866d6795c9e5ebe` |
| `Representation.CuspidalSupport.TotalConjugatingCountProof` | `6269ed6b27ffa578a82a3f6c6d20702e1e96907d1b6e6ad31c6f40afdaf22e3d` | `f4073a779fc3e9a31fdf8faf9a860b03f378b415ef68efc0230620f13ad6ce9e` |
| `Representation.CuspidalSupport.TotalConjugatingCountStatement` | `2abc2da82d63e7d3d0990232003e3c1647149a1463a28ffa7621da700e8d1118` | `0448a3105681043302fafee9291bbffba6b48c28c6e520e15c1733760f14030d` |
| `Representation.CuspidalSupport.WholeLeviTransport` | `159562c5f4a3471e41af6b7311a8b28d89b9bc724f852b9a7e406deaef588b9d` | `2fea6b0edfc24a9c0550ce79d3d8397492add447a0003942e6199248852934a3` |
| `Representation.CuspidalSupport.ZeroRankEmbeddingProof` | `a5631a32d269d612a85822a332c5fd3ecde85a30803ff8fc8f023d8fede5fe61` | `e85e35c3125c7297420e8bd486ffeee2ac301d7c38161bed4a9134bb2db49f01` |
| `Representation.Derivative.GeneralLinearDerivativeExactnessProof` | `7b00bf45fe69f8748576f2d32bee52a99034d7ef628288f541fad2022012a195` | `a9f72dd2aac8e765490d9b6e5f27dd4a3985960bc59bacac977b8d0527c9039e` |
| `Representation.Derivative.GeneralLinearDerivativeExactnessStatement` | `07137f4c3fa3e8e02ae87d2db953ea74cbb68962682a16075c66f02eed581fa2` | `108f4882d805861930e979b140cf80d73cc60f48369fef83530e64cb35425b3b` |
| `Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary` | `c6128a697779290df7b5656eb9917953d8eb58764fecefbef3ca2b63cd2831ef` | `e22035c1a3660cb208062b11b07c762ad1b57d240cf5a19f1c208dc3d7adf0fd` |
| `Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` | `ed442e54a4c8f750410069d15da60f64ee06b90328d205cdf89be71e8cbd6dc2` | `16eae8877cdd89ec2903aa6c4ed4292eb5a8ac01f74e3d6a0050abcd227f4f35` |
| `Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement` | `86079d1db18c19bb4fed9f11a683839b887c354681e20a83cff7d01c2a2ed514` | `63ba50930e94e922f862c6f424d6ac09e1dca4308b8751cdb9e7f1a78681faac` |
| `Representation.Derivative.HighestProduct` | `fad3466573f5c5f432e7c2c60537a7a1804b37e9c5de218940b388dd2b8276e3` | `b51380ed70dd77f56e20cdd973a6fc8e64b36b474a6844bc76ca3a4c7222457c` |
| `Representation.Derivative.Homogeneity` | `93070ffd89ec0f58a8bb256e7714a1c637efe612db946ebcae89c037925ffabc` | `c3b5e1c916b681f21902386e0216029d1c9607dd56095a63eac52fed57fe6062` |
| `Representation.Derivative.Iteration` | `ab8bbcca5fd7affabf804d6adbe09bdf2d578f961d1149a3182e6bc5a7a9a25b` | `056e0b7c6718776422735f35b44ca4749b31b5ed176349e9311460eecb880b1c` |
| `Representation.Derivative.LeftMixedProductDerivativeProof` | `5e91e3b36e0732f61be3b6e5b702704b0547f376ffd763cffab948641049ad4f` | `e2b990a18cb7945d50ff5378be4a201529f40282637175341d8e96a8947920aa` |
| `Representation.Derivative.LeftMixedProductHigher` | `1ad9530828d679d0b67870a92146f610a0d9ba501d06d7ae7735a52f4e468881` | `7a74a1d36599f66c32d54f731dfdf988725fb180318db8e2536188e7a83d2d55` |
| `Representation.Derivative.LeftMixedProductHomogeneityProof` | `871932a2f448225b4741e5cb04653d2afdbfa8a541fd0f8c43d356c1fa23a4f5` | `c2d56c98b7b9f5cfeed9eb1890f97c18f436fe885dd27b2ef1a8fa8ea9ff66fe` |
| `Representation.Derivative.LeftMixedProductHomogeneityStatement` | `add98a02cc9aca3c9d9eca686dbf8de538b01d9211d2c230435a97d6095b63e6` | `7f0ecf7e031ff0bfa9986cda1aea0c546df5ee16b2ab792df8729e894a5760c9` |
| `Representation.Derivative.LeftMixedProductPhiHatIterate` | `b6fb51ba218c6e4f1e208f28410f246d93ecb0d3588f0a44a369645f26ab424e` | `1cef7f5df895d150684f7ead333fb1830f1a0c8993f837e48d8a6549dce0dcd9` |
| `Representation.Derivative.LeftMixedProductVanishing` | `577f4053da9114447c46bea2497d482b706df5b011887fe771f7a76df310fed3` | `b7f998ad437f4cd507ea459cd18b967b450ccff006fab5daeb4b1f2125bf7438` |
| `Representation.Derivative.LeftMixedProductZeroRank` | `441c416e6a107a58548ca39014eff0a3c8fd08c815a99126eac6f84120c4a8e6` | `626b75ca56cb0c75124667a4de8a6bd99720f7495bb2921e0e5dadc2a2de236f` |
| `Representation.Derivative.LeibnizIndices` | `4f020e7f670de31148408efde0f5302ed33ff43892f8b8585bf8e72f8574896c` | `7b523739c3e002ee597625cbd25f50a2620ecd10ba2a91f9c08468fb12906501` |
| `Representation.Derivative.LeibnizPieceCompat` | `7b8b57b3cee75e3e4b854f6a9e1aa833be7d2823f166af2d8d2d73cbe01c6ed8` | `a2249aee9e4e8c15e773add3709078a431600f6408806e246f5d13ed22fcc990` |
| `Representation.Derivative.LeibnizPositiveGluing` | `a4a02592aefca6f2bca42fbf2a450962eca9d61d503eeb804b481e6a63b7cc1d` | `a982585a4021f90fc187dbb8d37c90b740b4e3fa91362bc6d6750ad3901ccb60` |
| `Representation.Derivative.LeibnizQuotientPiece` | `3b34259562d7985494eda701ded2067c94a94a2c55802f13df8a26e545ac4ece` | `84e871452014c225600bdb0cb463cdaad357181a2537a86d0aefeb1cc5c29c0f` |
| `Representation.Derivative.LeibnizRankZeroBoundary` | `4fb7f383c7ce02dc7c03fe437b4e1061317ba2075d31badb9b1ee28e21e7b1c7` | `2ca38f75cfb118dd456d2b89a6a7c001c6dd4f302cef7a23bbedd2fc1c448297` |
| `Representation.Derivative.LeibnizRankZeroGluing` | `c4328689eee0d1fe67e70c1c7390b8cd72d8b437554f8f3bb800789181deab44` | `d06098c8e6e3808d22ec60572bc67ab0b49708c450723a1f0dc0711fff6d376c` |
| `Representation.Derivative.LeibnizRestrictionCompat` | `eec047a42e966a9a064c2605539f8fa96c617de8d7eeafb119440688c5959399` | `e8abe83e3c3c6ce8a63bac2552d1f4a7a2426df1a138de8a9056f3a0f84a965a` |
| `Representation.Derivative.LeibnizRestrictionExact` | `d4de3697b588051c5562e2635377eb21d99bed65cdac92085ce9ae33932512bf` | `671eb48605b599ad2f3278d27bc2f220d6e41be42e718ab930d5f9e9a6ae8c58` |
| `Representation.Derivative.LeibnizZeroFirstPiece` | `586d0ce13b467ae13c86a353099fde77eab3ee66e31cf1eac4a32dd6134dbba0` | `c076434c4290294aa56124d3594e47e517c8d21abd91d8fa91e36728dbc7dedf` |
| `Representation.Derivative.LevelCalculus` | `4d29f955a0eda82efe74a58ea4dcc91221c07f0cc94423ff44ce09457fcfb8bb` | `675481e2bee8e0b4c060d987499cdb67860ca617ef7978bef6db91740b3d1ae6` |
| `Representation.Derivative.MinusVanishing` | `51e7deb9761f977154a559595fb0138e670ac78be836af680404577635e8808b` | `2de8bb8a57a2a1762e6c7b79777fb68861300de3f58d65f49738516313ddc0a9` |
| `Representation.Derivative.MirabolicCharacter` | `27ad9768aa1f5ee9f1534e99521462f22cdb280abbcf711b79621d405d654a6d` | `f7b710cddba2ed791d268d8a1644315548f2b64912ffed0138579cbd497fae25` |
| `Representation.Derivative.MirabolicDerivativeDetectionProof` | `db09bf1124fa22ef6954e26de0155723d9627c332bacf36f98bf1f0278930cf2` | `99ead1407eb59ea71e40549d91bf96cf38d842f61dffec1e992cfbe534b1eb36` |
| `Representation.Derivative.MirabolicDerivativeDetectionStatement` | `41824396183c6ad18890a7c51ec5f3c0cd1a0c1b66803c4078f85fcf32d038ab` | `b8540cb2f3b19c71308e6f66fbe3bc0a2096f68b74cab7015d76cf51f16771d2` |
| `Representation.Derivative.MirabolicDerivativeUnitInjective` | `ba0db2ba3ece3433efe8558dd19ae31de528d967cb876cdc6b60ff256a35c6a0` | `830d086b535ff3b76466f167414687a9c526a9adeeaac14821c75ceef84fde84` |
| `Representation.Derivative.MirabolicDerivativeVanishing` | `5a7769afe378876844a9c212031da102f591bf80b11190b0914904808e4c14e8` | `a979c2d19534f38918acdfd6262e01e5d6c671c185156315dc0b7879a9bc9957` |
| `Representation.Derivative.MirabolicDeterminant` | `98625224702b6c0f369d1295071d6b6a1abaa91e0cd6fca60af5026f2c7c4adc` | `87817063ec4e923b50df30342f4fba03acd0e26fb22fdcfe138bde0223910947` |
| `Representation.Derivative.MirabolicHighestDerivativeDescent` | `bc34f85bbdb360064f768f7547552664c15a51291feedf8332480e8b32e19460` | `6c8a26a9c9fabe71b5ae811250c83a43c374746f695e11c6b3b0373338edb91f` |
| `Representation.Derivative.MirabolicHighestDerivativePairingProof` | `8909dc9cc17b00a0ae17da5b32442c5876c934d4316b7cc8c9c7c2fb51ce7e6c` | `a37eb9abda35346d8aa9583eced7405821d05a817ac8764eeadfb841be000bca` |
| `Representation.Derivative.MirabolicHighestDerivativePairingStatement` | `d2e108375057b5d0639f83d51431e758153c54126c00695a69b9062fd88623ff` | `dbf2a042a007c94dafa9455d1235cf5b5cb4fe711aa0ae107e35fe9b739ac294` |
| `Representation.Derivative.MirabolicHighestLayerLift` | `9ac1a4a5a75b22b0ac3b63393288781ba48775566b3cd9d3a83f0cfad9537f94` | `9a60c20501794e569d3ac59f39eb5bb122a783fec63beea8b6ef75461a62b2b3` |
| `Representation.Derivative.MirabolicHighestLayerPlus` | `14bb209d1044412168a508a44a560ca616602e0e9c8c494a4da20ee2f9ff8a59` | `0d27402a144d53a1841d925361064e0c33e49a294c251918530f760f6622c98a` |
| `Representation.Derivative.MirabolicHighestLayerPlusMaps` | `7ad115777adfecb1aaf9ea262a54b52fa7099017ecfff28e53eb159b6424f3ab` | `39a5b7ea8ff2b1692067197cc15f30cdf40303730b8db0b54570be02de7aa573` |
| `Representation.Derivative.MirabolicHighestLayerProof` | `2f268182472ae941c1f4c98d950c9af506f5722aed2ffe130674399016778a5d` | `1350f562b2f396e7f736d3faf647672e39d5789858db097b777987032ba33e39` |
| `Representation.Derivative.MirabolicHighestLayerStatement` | `18167297f5a3657e1b35b1d09a87eb24430248f08baa2bdf9a1b46eae13a6c0d` | `038132bad17090900b65626b9b168205e311906d32c96ba4c6e5eaae49e588b1` |
| `Representation.Derivative.MirabolicLatticeBox` | `7a4ee4e1c5c73117c7a8782c87ba4636888050403656f71c29b4c488a49d63e8` | `7588ac8f643b93763c63f2ca336d240c18fe75159734d6480d81218e92e15bc4` |
| `Representation.Derivative.MirabolicMinus` | `526932155b00d435068485ffb7a8a5d4f565b9729779cebe97cfcf96e894e02e` | `3b6fbca0a52aed7251fab742229c22ded359759b67326d66f69db5c1a9b0e9c9` |
| `Representation.Derivative.MirabolicMinusExactnessProof` | `8c21a59926d980e97786febe258d9e56297f8a9dd89788d23bac065e693d2ff9` | `0a4cf394c5f701bf1cc209a5463361777da5cf1a0273e73e849d95709f884a99` |
| `Representation.Derivative.MirabolicMinusExactnessStatement` | `729ec39dc9dbff29b6a8b9266e6c4126e33b63fde687d72a85f06203a2e3d5d6` | `5a1d39813e2cef1659e036d4b287ab9acb76da2993ce2d850a2163d6a4b09f82` |
| `Representation.Derivative.MirabolicMinusNormalization` | `fdc1fd8583588ba1ca5722d96f91b455ea9dadb494b5d8a22ec9e96d789836c9` | `06468be815383e4f98fe355fb5319430a986d5b93115ad2befd16ac6ac3f515a` |
| `Representation.Derivative.MirabolicMinusPairingTransferProof` | `36b55de0f6f0f89d27717718c14350e2f836f4d6786a0bacb4516844bc4e9c5a` | `3f7f27b20da3f6d7f838e99dc3cf7a964789c1e0160cd58bf50ea6cfb67b48c8` |
| `Representation.Derivative.MirabolicMinusPairingTransferStatement` | `122571aa97039204355ca3abb36ab1404ae8b858cfaf77f814c367bcc91ca8ee` | `43ab5a66f8bd80921a8b4fcf25288ed6292eca25ff29a7e9f4d50b01af78ea29` |
| `Representation.Derivative.MirabolicMixedOrbitCharacters` | `7f8936d47e70e5945417457bc48c3319958a2adecae704e0eacc6b286b4c1297` | `20ad3d40ee8d844e6badd8564c1957a9a20b42723ac761372bfef4110f0c646e` |
| `Representation.Derivative.MirabolicPhiMinusMackey` | `c709db9ce33d20dece2565f1af875a51da168dc5ca39d5fd94f330c78f989546` | `aade13d8f361033ae3c2544011db1c3548400b16f2b6db387c5a7224af181900` |
| `Representation.Derivative.MirabolicPhiMinusNondegeneratePairing` | `a10625c16e1f3eef270075eb8a335fabbb68532efc4730c1b8c14af8bef41207` | `5153132347ef2a8a156d9a5c7565edb5d4f65223865ab943ab43af551efba81a` |
| `Representation.Derivative.MirabolicPlus` | `07129014f7995b8bfc85636fb59192ab88b8b9cff9a63ff862a14fcdc03ab421` | `62e65478b9b3b0007744b3409f7dcaf68275f2fcb9d87f1fc7a2ba7441112798` |
| `Representation.Derivative.MirabolicPlusNormalization` | `595ce946b02e177f66379f9f449fadaf8e82ea1eb872dc146dc96543e52d5c0d` | `a4cb8910f86b4dff1dfe1618b5aff3681645c21a6913b3cd3a264c739b29ad3c` |
| `Representation.Derivative.MirabolicProductMinusBoundary` | `65072598036f0bf2e48136b9d107dec15ecebf0e2640a1939c2488b77f1a286f` | `aa149423537b449a4e72d48e0dd64dca6fc67a4455caceb8fad9747c4db88367` |
| `Representation.Derivative.MirabolicProductMinusCompatibilityStatement` | `e39fbfede231f478de63bf569a72d8d4bd661f3e6f4b5d1c68dd50dc8e50be69` | `0d7887f87f00b6b965ed1aa3f6b941faa091137e97f35867ebb8c31406022d27` |
| `Representation.Derivative.MirabolicProductMinusLeftPhi` | `fd96f9f2e8fe28b5eb36d53031682f8b61078f71be003bd1e174e1cc39cf4e00` | `afab0c259166d82150167aa6ef5e2c94d1764d5479b7b7e5db900557b2c00251` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient` | `3af34cf9a157c2a2f6bcb562ae301bcab348f127eb3a8e243e2bc8949685893a` | `7cc01aa9b6613b5a4250f6814f8989f9f9a4554cd30b84c647710c9155926064` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiCompactComparison` | `f4e1a1844de3e8a56927a0956bb5e0f9381936b9d54ed84359011c896a5bf2aa` | `f98dedf2397286535b9bff0a0b6d7b07cafa808eae23fbd80b2bae59d3e4c576` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiHaar` | `86df702d83807e36dd81cf5c2120316a4bc8b4ade99118d272daa3d64b81bece` | `6a5741bcddf57213080874265bc8a8c3b5d64fa218be3ec1e5ae7824ea8d06d4` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport` | `a5a63e981f8c6de28e1938ae655a59aafc660748ea7fdd43bd44278f92c85a02` | `8d8b9ce3b48d328f3146ee2aba9e4f99d36f9441b858da7fd387d6bb556a7dce` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiIdentityComparison` | `c2295414cdbe8c48ab87b97a9fcf892f7fe9c86191f6aeea529278842cf3cf8a` | `abe8ed5a77c652558205ba21ae37eee6556783024a8c59da06a3b3737c8a1516` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization` | `160f2b192d90cd6673f79457ca0feb740aee3204ca3ed5983f5e6ffde3a6cefa` | `bfda585cbe3ec476d41b5c7bd89b20d85f1b6b8896fc7675c5b8633b399efc08` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiLocalization` | `90746b972451e7f072fded873c3ab257aeddce08080c6a146c54bd8b19797ae4` | `886f4b69541d2c1de303f5fe06981b96412c603f413b131afa3055eb26febfb1` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiMackeyLocalization` | `47ab82420ea8b9cf6da15f0ec327947cd93a104efce6283e9c4a37014b9f16d6` | `a72429b581d11c482029c71ad0c1dd3d640c8a13cf2e31f5b50177cd0eac34d8` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiNormalization` | `62dec9fe764fe4d14731bde9dea4354ad901c47cfaf81dc93b35f7a9e70a821d` | `a5db7bf727d9612bf0fd4e286025966ed5739d68325bf5d495ecc52866d0bf41` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection` | `d2fdacb095a96a36a6f1c4395015c0ec5e530759c00cb1e9beaf25d92bd4cd50` | `2161d9e455cc5e9ce566ca444f5e385a3247808a6d4b4c41c1ff2ce469889553` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiSection` | `b1bfc307555aaf2065125dc0ca7d568e4d23b0028abc5dbac102e9ea04c72a39` | `d12e4c0aa6bf35e640fed85b31e631f71ca912d1d9a7fcef754fc81fc1ffc05f` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction` | `c7e7e464e49c9f6161ae273e37906e7c77fbe9b069da48849c06b645d4e56e04` | `9fbc9caae7c9e717520dd24f86b763401881dc6df5e9c2e6303fc0f010afbb1b` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison` | `d20c826956480f9f895ba01172cddce4688fb8f04f86e2d7c63ebdf15a406afe` | `6d099219922e3a112567e7708e4ccfc586fe58d504a58ece9524ff73550f81cf` |
| `Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison` | `e8c3aa36e5dba03f2057be2427e5a4af4283423023a2c626641e884013f179f8` | `0d805204498417149499e61840af5a83cc3ce411946fbfa8e6eb317864ae078f` |
| `Representation.Derivative.MirabolicProductMinusLeftPsi` | `55824f5b99bdc6ff741ea0c460efd7bd52631df1cafec1dd76186473267b53b8` | `8cd4ba7135b9fad4336031c5861f3b69be2b97a51b59917d05ead3b7fca8b288` |
| `Representation.Derivative.MirabolicProductMinusLeftPsiInduction` | `6a9ddd1306e4c27a246123b4801934493e16d7522e0956384f7fb38a971129c1` | `58fa5a85109b53931d9d527a530b626e3451fb4c41b78bc25693594be077854c` |
| `Representation.Derivative.MirabolicProductMinusPhiKernelComparison` | `243ec8b48d69c059f43e0314b6ff98063e80c296375bbe462cb024044f3c3846` | `f70a7726c2e38ec015e7c05ae06512b5582e0965494d4998bde19c93d283f698` |
| `Representation.Derivative.MirabolicProductMinusRightBoundary` | `04f697ff2f5963036516edb67eab9b0971186fffc6a551457830cf52222be42a` | `d2680288fd1cdac3301f89895c987f43b7adcefb074c5128decb6dd608e11d74` |
| `Representation.Derivative.MirabolicProductMinusRightPhi` | `a72e3014eb37ddd3068b4bd94369e95380dcbfbf8078c17b4ec4bdafebfc468e` | `f449d524695ba06d1fb5a8f136f23afda170632285bf4271c3efcb1162caa6d8` |
| `Representation.Derivative.MirabolicProductMinusRightPhiAssembly` | `ad549c94fa37f0c0c9e389d15bb174ec6960f29d2ec08c7996a47d9d540416a3` | `2c76043d01ed8f2ab70342513341f03cc5e9edbc31f6d9995217f80acac21a7e` |
| `Representation.Derivative.MirabolicProductMinusRightPhiCycle` | `6f77f1cba85cec9f82922c1c2d5073d02e4e90bcf64c91e4257d21668a4da76b` | `aa0073aa7542ba68f126d2dee4e0e11d8d1792b481dd935bf44a9c6a584969c1` |
| `Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient` | `deebd59564251316f78b26f9e1758691463f182372de6e0d1f7c64c367ac2efc` | `32f43a1dbe05bf6fbf0b1b2ec1a042868efb7a1285fde423b96874aa107acfe8` |
| `Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups` | `e5b4a3ec7fcb7192576e41718c6870812f0066f229dfa935bbe0c22b32bff1de` | `100572dc1bf096513397061dc837ddb2c4e45cc74185298126d6dc0fdf2a5c85` |
| `Representation.Derivative.MirabolicProductMinusRightPhiIdentity` | `bca16ee399393cd5752d86bf5d1d54890416e65d58b49921f8d18d7509fff964` | `ab134669877210b8cd238c98ea77a693af6ef0834e4190052829148da21a2c80` |
| `Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient` | `23029c3383523f9e4f99027f037c410be973f3d3ad8a7999c7d48995efb2f3e1` | `26c4ad6b2d6d26c5af8d2b17b52f043d60371c3145d58a2c26596a4eee4f1c87` |
| `Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups` | `1e76650645690bd94e007125c715bfdc7e3a89272cc9a42e48e5c3834b84fb5c` | `90af2c1d588fe44ee65109fed12630c692d3ff8f2eb11508148da99bd2ded158` |
| `Representation.Derivative.MirabolicProductMinusRightPsi` | `7bd5817e03a3b7064a7c81a1df148e97af036c03bebdd3981e35091f1eb711f5` | `45d54201b8e93e26ccfed8a155f340db07aba1beb9372b9d62c9d1134d3f9010` |
| `Representation.Derivative.MirabolicProductMinusRightPsiCoefficient` | `555a28892b0291d5a86a99d07a3b1c2eaf11121e6d091b6fd0d3ba2929ea98b3` | `d3f7774b363fc3240811cd65a8037085d2ee619b2e1fa6d26fb3c71d64a50f84` |
| `Representation.Derivative.MirabolicProductMinusRightPsiGroups` | `6cc69e0a38e5352ddb09a6e202b5c04f23f74872f3fa454efdde18be26ccc3ee` | `f641dcc287a5cf87b1b8af99ea8310cc08b0a62cb8cce62bbf5fbf63e9d4c5e5` |
| `Representation.Derivative.MirabolicProductMinusRightPsiZero` | `88dfe22590dd40856dc95bcf1547d9b5e6ae1558afc14ab07e1167f1bec4f578` | `06adeed66cb681c2804dde6c895653f861254017bf025a4e87139e82264d9e04` |
| `Representation.Derivative.MirabolicProductRestriction` | `8a15d8eb37a5cff83943cf7bf7cc241685733db18f7cdac470d861c1c6cf4db7` | `95c6caeeb30ddf55e0274265a59a30982728b4536ceed3bf495b29f8c6589974` |
| `Representation.Derivative.MirabolicProductRestrictionCasts` | `3565aeadf43e31a684420926278b2d370ebf4bc108d10aa6392ecf631f901304` | `c2aa711d1687e22fd8e9b85603a29dfe7ceb475021363baa2258a9a7b6fa1e74` |
| `Representation.Derivative.MirabolicProductRestrictionFactors` | `0f85e139fcc705788b699d04166b10332e1dc66a942a1028e68f02d699356e4a` | `6b903444cbe9c0ff9943607e3f4af9ad8d4147e273c485e43776c40153b83508` |
| `Representation.Derivative.MirabolicProductRestrictionMackey` | `ed923f1889fd6a777f19ed9523a62029b2f721bab8664ab5599c24f6e4343e0c` | `8ff94fc6f03bbe8c5d9c18649c936f8d71433184f77d5d7abcb7b9105a9465ec` |
| `Representation.Derivative.MirabolicProductRestrictionOrbits` | `bd98004483193a457b0c8e4a51d767c919298c5296dc39524af6e76fd65a54aa` | `398a383f72224d79f4e2c4fa1af625844d66f1ca15de8bbd858cf88b9eea2750` |
| `Representation.Derivative.MirabolicProductRestrictionStabilizers` | `aa21f4dd195795a5e720460a05ffe58725cdab4da57dc20a63b904ad22f3b8df` | `9cb6f1bc828af897fae228260c07c634a72faabd11117689d74bad1110471173` |
| `Representation.Derivative.MirabolicProductRestrictionStatement` | `fa1d89dab7c3c93cf8ae3d8eb7b333443c2bfee49779430f2ed84ee8d95968bc` | `05abcac3670216f33ce9fe655f859b07ca5d2ef27b71199134324669b4798652` |
| `Representation.Derivative.MirabolicProductRestrictionTransport` | `3ddcc45fc0902c0b6b42239b3ead645e0584a92f0236fc18f82a3e2670952894` | `89e62d1f0107fcbecfbf6fe2d954bb3ea87e411187c7d101ab2b6cd84c71e05b` |
| `Representation.Derivative.MirabolicSmoothPhiPlus` | `89c6fa0d43f8dc8246831aa33bd7c8b70b247285998bcf44e6f21432f3dd8875` | `4eecd63bdd6148aacefa102d905712f5efb877c41925c9b6838f6d99774a7844` |
| `Representation.Derivative.MirabolicSmoothPhiPlusAdjunction` | `55cba4a53f588ca8c51b7352c7686607764696aa91e545a06a22f4b4defbc92b` | `e0a45539e5ba68db1424eabbb75e6985e38a8f29c2faa75c6db378ac099c7843` |
| `Representation.Derivative.MirabolicSmoothPhiPlusIterate` | `837d4e39065c2085125685529e9d63331a908506093dae2464f90891437e8e95` | `d4d16fa822a379ac7ed301d4eb6b50bbe9cf5671bfac0fb012a3dfcb322f9a64` |
| `Representation.Derivative.MirabolicSmoothPhiPlusProduct` | `0cb10e6f70d6d98270afa6fbbc52888f0a913c15d4c430b0f382c2772ae95869` | `bc185ee0a21926176109d4b05944d7a7c4ef7d9473c438c678049caa3facf763` |
| `Representation.Derivative.MirabolicStrongIndecomposabilityProof` | `bff0fe54e9316755955e8e64eb771bbf9b44206e6e22682c57cca6b3fa7d93ba` | `c30e86cd68b12525a6160ef7313979cdc20f026ebd640b18f3d55e70134f487b` |
| `Representation.Derivative.MirabolicStrongIndecomposabilityStatement` | `e012df3c329e774cf5644314b1635927954c3201a58d96058c5a87712f47ff3c` | `45f6d48d1ddc17d45477b9405883c6e4e3c3e33b8c2ac416c22f41b8f3e49cfa` |
| `Representation.Derivative.MixedProductDerivativeStatement` | `5936546c07ee475af20142b9891f021e02375316ead2230829fb15c8bde5d45c` | `197b353eef0d81ae27ecd49f5e32fb9b971d760b1225751c98a740f4687f90b2` |
| `Representation.Derivative.MixedProductRankCast` | `f3f16af86824a438263f99964ac7a3428c832c3f3965a37c4edd06224c8a3347` | `7ec4de9762023affc851f7e308f5a228c55ae601ec7fce3087bfae83d611ac2f` |
| `Representation.Derivative.OrderRecursion` | `57eb17719f73417b28b1d2f04b196a77579433cb9b441525b9c0aeb5f6ed0976` | `c2e6abd204050d5c828eb9bfff0ac6d5f468fb68592eb02d80f2059ee6cb2ecd` |
| `Representation.Derivative.OrderedCuspidalProductTwistOne` | `ee2ee5d6a8c5faca2bbb287697e595adb21cf477c5bb6de75b3d5a995d5e3051` | `e06fb071eb661f5cbaede22586af132b61e51c5d7d259ab095b0cbbab653b922` |
| `Representation.Derivative.Partial` | `8ce775549e42ea92dff50d9cdf5d72eeb9cbd1662366929c01a4e80d09fcd22d` | `b776ae28bb912e867ec4962b98ca8ce260e642facfdfd4ca0a40ca7e853de688` |
| `Representation.Derivative.PartialDerivativeJacquetComparisonProof` | `070f70ae615f5a3fe00827659167e0af8bf3ce615636fa00768ba584b84a7d5e` | `df5fb2a2e519b85aa778bc4ebf7ed0ba61e06622b0a1fb0a0d379af1a71c3cc2` |
| `Representation.Derivative.PartialDerivativeJacquetComparisonStatement` | `0233fffab0e03145ee53e3dfe4a9f9fdeb0f0d3cb8c04a740294b82d3d1860ff` | `b68af396fb4003df26cfd415a96b95319c0cf6c53906410145e29dcd4cd99983` |
| `Representation.Derivative.PartialDerivativeJacquetLHS` | `d36f3769a9182cabd5b3c0cbe5f3fc93b8411b8865bb7d7d5df1999b0a28716f` | `ca45dea558319ad062c33acdb882088c0f52040a3023db3948ea795d55fd7311` |
| `Representation.Derivative.PartialDerivativeJacquetNormalization` | `8d7aa2b88f6f6b2b41ef9a2f4a9e4a5bc8ab824eab4c6c845c097bc7de0e46c4` | `e12d35c51d2687f0744cbbec06f24573a91b094cae6eb15fd88bc76b409f8b2d` |
| `Representation.Derivative.PartialDerivativeJacquetRHS` | `6e78ed7347a8870d898950a8a07667890c94bd7186b7678be6daee42fdd4a7d8` | `a5801ebbf803285efa05fbdde1a3fa4523806cc336d06c4459743d7e77cd773d` |
| `Representation.Derivative.PartialDerivativeJacquetRHSComparison` | `62a2baad87445590464d12486065de4adc1f335768bca745a1b8ae65df5341e1` | `71b7f064c379bb06c1554d7ec15f921c24a6cd88c89f2c81cbf5ade3cc6270f9` |
| `Representation.Derivative.PartialDerivativeTensorLocalization` | `936a330c4475e2968cbe5355621ec6fc9957f966bd4eb76c2baedc19c3c732f7` | `3477c65aaf8c65db063b4316801295bb067d2dc043667949dd306e21fc6d0a82` |
| `Representation.Derivative.PartialDerivativeTensorProof` | `9fb021bfa71a25f488a579aca3064300290ebcc1fcb98d1619ac6e5b72416077` | `2a4c18aa8e45301eb73f2ae3b82b26cd05b2dbf0cb387715fac9852468849a94` |
| `Representation.Derivative.PartialDerivativeTensorStatement` | `30c22587bab476fab8c6a190841b30c41f8dfa20b9f40b0187254c3f53227f41` | `e21ce266515ce4c853255f63bd98c8dd5bb097ded93fec62c9c329415b5e8c15` |
| `Representation.Derivative.PartialLocalizationCharacter` | `8b893dd94501d4c1389842cb7c3906e00938bbef98da27af57923dd31257544f` | `fe57a56d0fdc5bc51735c4ef4782d5aaea0a28107e6538a2642d46a2ab212f67` |
| `Representation.Derivative.PartialLocalizationData` | `358e8362bd80ba85c2d327cd4cb6c0d96a4289c85cd0cb0e1af1e316cc33c637` | `435e83105b43630597d545bdc9d64e04adb99f6dd9e5b6dcaae06f469f4c3ad9` |
| `Representation.Derivative.ProductVanishing` | `125b724fc96648da9243d647dc7445f5eaef8a80def1ee0a2a43643897de3a38` | `f54e707fd0a6f5c07e0f625919889660c77caf0e0ee63cd4b88e185a5af6864c` |
| `Representation.Derivative.RankCastCompat` | `1589c79de47edab59c9f3901f0f6341b3e50ba2df5403bd1cdcc25ec5d3db343` | `4f7e7a6ad31fdfb79269920a45ebf3aa2fef2510abcfd9209bf067de11a143e4` |
| `Representation.Derivative.RestrictedProductLevel` | `2cbe6c9f9d38fa5a3c789a5abab57100763b4678a67377a9f364435b1526d0f2` | `93ce47b41222d07223b3c484e1242f288fd4b77cc3b64c509059a01504766f2d` |
| `Representation.Derivative.RestrictionBridge` | `0f488dc2fafbdebce4f8a6d31abd3b7a6c7bd6a9541567a4ccfabe820a99d2a1` | `863704730c46526fff73e8d81caaf2006e1f6eff780c37b394dfd557c2e8eee8` |
| `Representation.Derivative.RightMixedLevel` | `44f743aa9b3e1ce650a5c878277f8f589f5d9a141f1eb450c4683f38d2fab38f` | `e7838b207b35fd14a68f8cac5c31bfbc59badaccb3ad1bcf2c6b145f952d458a` |
| `Representation.Derivative.RightMixedProductDerivativeFiltrationProof` | `3dbb8b56e18e2240fd268f04f7ea5b531795c5106a60a3587e1010dd33995d91` | `da6754be8063e15f441419b5cee73aa22ae8198c110401bc03f659e48eaaf550` |
| `Representation.Derivative.RightMixedProductDerivativeFiltrationStatement` | `d7136ef2a0db225c3747af48136074ee76d91f831b9aaf06d597b059e196c482` | `92ed83b56583d3995e2e0d1cdc0a6650bcfb1bdc9bb61af989dae02818b9db3e` |
| `Representation.Derivative.RightMixedProductDerivativePositive` | `39186a0f1d537a3a3444ddb10e8cee5bc5645115576b5d236b1da20336975c0a` | `b16a68929c852486293a6032f1b97d965c2caeb64810b149fbc66b7be55cb546` |
| `Representation.Derivative.RightMixedProductPhiMinusDetectionProof` | `87a8e09eb39775779056e881130dc08990f09b6c7a750096609942be669d5bab` | `9020a2d050760efdf6bbb5fee6bfae7182dfcea4cd1efb4bbe87b34dc1b6a26f` |
| `Representation.Derivative.RightMixedProductZeroRank` | `574fe1f467edf0327595577fb29b8107014d287480d25b8c06b83af5df359e1c` | `469d1657d4bdb9ae08d9daedd14b5a49484686cbdbcf1fc01791453ed7cb3a27` |
| `Representation.Derivative.ShortExactFunctorLaws` | `f0f45150c632b11ea2f6e5a0dfc776669b1bf0321a64c684b847ab7f55694163` | `ed32ed2dfa76efd403d7a8c3fab7b97fb2383dfbe9414052c3be1f72ffd7b75b` |
| `Representation.Derivative.TopLocalizationBoundary` | `8e04801c57a55b443dd6df32a7f9a2eab292d6cd29959f077068e7a7b3f0feb7` | `c6bf8f65e9feeea7c2c78fc86308b25df3849d70dab1448cbe61b5b534ca9ff4` |
| `Representation.Derivative.TopLocalizationComparison` | `2783e60fc942829f2def86998823390808e973588b69e9cbc4209322e9f332b8` | `c08ba8d76037bb784107d7091810c113169dacb724f2ecb32c0182ac71022d3e` |
| `Representation.Derivative.TopLocalizationData` | `3e614d4ace28000478f262528a8f9127f5469918aa3c23aa7942e8d522fcd940` | `ffa42542b918bf2c4bc8c866bcadfc52b20468d89196d7411f14bf45ae461f6b` |
| `Representation.Derivative.TopLocalizationMirabolicZero` | `9a96b67505e6efefc90b19a49628a43c153507e697d9e7fd0f1fd7675db1b98e` | `f4395f08f215880bcf48aab79d511637a1b15c8a47b3c8f61054b175109c9d88` |
| `Representation.Derivative.TopLocalizationRestriction` | `546249e9097bd2d7eff00538690e74d3e1b6f27077de8789b00ea2024a98acf6` | `d0a370998a3bce2cf8979d0cda87ea791433c1d59991fe3691bed11730101c41` |
| `Representation.Derivative.TopLocalizationStep` | `ceff90bbceb30fc65a4781dd430d09491e399c154a959defd3ee2d0a4226e731` | `f22215d35a0b82e3713f9ec8d1e939019f87f021342d036cd86f75b3d3c5ef23` |
| `Representation.Derivative.ZeroRankTensor` | `33318f457575f60115738ee46705977e1b90edb51b8f2cd929ba9ab59428fc7e` | `7791012e2619b84c91193bc1b6fcf3f665f6f8e3e3cc365cc33e81652fafd9a5` |
| `Representation.Dual.Definitions` | `53959e3b6cd0faad27f2566cbc9275fd537e5ab59d800f453bcbd61d05415ae5` | `bf9972bb15d854ff605ed825fdcdf90734dc924ad0ae33efb6bb4e55a882845a` |
| `Representation.Exponents.Central` | `ec9eac0489adf392dc2b94dcfec664f41c7ce02a310007d86d0c9341d8ea0557` | `173e76107b355511c75435f04b996c3ed7998a4056d6f4f8cadbb8a82084c290` |
| `Representation.Exponents.DualJacquet` | `218fb81da3d331047b7be542656fb269340268ce24b93f075d8849df4b95a608` | `045b65d3f52320e66226f05317e0a81fcc4685fdfa20c56faba313acebe4234d` |
| `Representation.Exponents.DualJacquetStatement` | `d9de43e187719840878aec110a196b099434c617383876f5a7db8034a41877f5` | `9d2de723ea280bca05f7ea4a87aaeac93ba8ad18aec60db24075b40519d9afb5` |
| `Representation.Exponents.Jacquet` | `836a1c96a0c19cad20ad3fbcec47068bb0ae3a49d24153e8ef472141bc437a01` | `153afa3ee8969513e4cdfa22d0d7a9ae6a205ddd52cb8ddd3db2ae97a951bf08` |
| `Representation.Exponents.NilpotenceIndex` | `fc8d862b678231393744b85518060d52ae05059ae59819a78637b86311bd3a5c` | `1725e1926f1e8123699e4ad7a7e9c23d8887e6ff88d2bfd26d8e49bc0167721a` |
| `Representation.Exponents.ParabolicPair` | `13aaf2efac9446a5de70599bc3fc7bb421500a870757eac7d47b36d05e811525` | `fdd9d4b783f5f888cf3dddcfa5df607b39a8493ae72a3ef14e31566cf6936c39` |
| `Representation.Exponents.UnitaryDualJacquetSupportAdapters` | `1d49afec155339ec01cebc44c54f6fb940952ad54edc9dadff8f13fab880be7b` | `613286a4f2c5acff4b0a50c0725b8e3c7e4cd146f8d5033e5c6074a690b990db` |
| `Representation.Filtration.CentralEigenspaceSplitting` | `e62bccd1f1a66809c76a7a3a8f22aac25b562080dd1caacbc36ca5c8b150361e` | `20493f49e929a04fe92015f4e35f6b31912feb238326e8f3d7258b89b8d3147f` |
| `Representation.Filtration.CoinvariantVanishingStatement` | `f5bbf6cb3da5d9cfc858a60043b198ca954d2f117cd8f47f62cb0af08c484c02` | `4b56250e0c46d54d1fb953d2680c07f6bb450f76dd58319ce29d9c5076f99e9b` |
| `Representation.Filtration.CommonSubquotientStatement` | `2f4ba827abb1df3d445e0a840ef2b00d2a77a34d0c584fa4aaad4c8c997d079f` | `e82acdde0867d2d8de32c9fe0d55ddb6de3257575b55019671c560f4513c79a0` |
| `Representation.Filtration.Definitions` | `c370a357f654f4608104c362c04881d40e36b2423d11a30a6e8225757c2f52ff` | `b43b81bd77a208dd68f0dac14b82705edaee769c2886a8280f0c430525cda310` |
| `Representation.Filtration.FiniteFamilyMultiplicityProof` | `265d6221ac1344613aa413ac5f114ce428921b826ea1f096efa441d175c1992e` | `f37d6536a3be357bf76a1f78a281dbfcfb5305afd83ad304bf42d3376a59aacb` |
| `Representation.Filtration.FiniteFamilyMultiplicityStatement` | `c14e28487ec3bcfaefebc91a42ffe8990255cb3b72abeec8e0a3e3451ca958c9` | `f142da846c0ea5bd6d3f2ed7451717da8589536bd76a3c6b76fa0f22761dfc70` |
| `Representation.Filtration.GluedFamily` | `33b459212b8e1beb3c6717f36c7825c4583c23eabb52841bebfe759b0e498563` | `9e22cd068878af2e11cb1c0ad8ac44b1b5f9b321c3c84c51d465e46d4743274c` |
| `Representation.Filtration.GradedRefinementProof` | `ed24a8dad529d9010901b89fe590e1ccea31cf11e431a3cee7a63646b58f3689` | `6841a038963350538b5c6c0409c490c3592037c6dcf138e6c61e01afb237b181` |
| `Representation.Filtration.GradedRefinementStatement` | `8969c2a76c2f616869471a1b4f8c564a03e74f88f8916082850fb0a523d96768` | `9f971120e722ecd99ed595913a403a6d3dff1cddaa2ff76ec368124068216c10` |
| `Representation.Filtration.IntervalLiftProof` | `146aa6d1cf6ce21a542887c4138fd16cf63b7249cb784c530da67d7bc26460df` | `e645b5e6b9e222d34a0c167e9d3d15c0ec6ccfc2c4ec5f7cd7d59e1e2ded24c3` |
| `Representation.Filtration.IntervalLiftStatement` | `cd1e01e142662b5d70c69f5255c1e3993f127936e4ca7da70983620ef77828eb` | `8611e352bcb0ed7b002fe256a5dc8131938c9ab85043746e364fc08ed25ca381` |
| `Representation.Filtration.InvariantBilinear` | `a81a2847e638aac7eb90cb2913ab5055312153be5dc9748607bffaa654dc4ec6` | `8036498e3a6e2f06bbab426694c457fe5d3fed60498bfd19521349ad379c1590` |
| `Representation.Filtration.InvariantBilinearBounds` | `6c219b28f6e3668a73221d7c88a8b1fe35aa95ca93b87414f41b4fa9b7d1bdd0` | `37e1aa46829603cc1a889f9279681166ac1fb77eb95de9bddc0f306cb7d2345c` |
| `Representation.Filtration.InvariantBilinearSubquotientBounds` | `fc1801714378b93051fe50ad36d7f83036b8dcad9c8822b617208194e63b4cfb` | `56b826cff007243dfeb6dbb3bede58fe434f4240ba05662a7aa78f6f971c3c1e` |
| `Representation.Filtration.IrreducibleMultiplicityProof` | `dfb57d62b646ddc9a44f05864db95f7536706e66678759bd37e7b2c612d0dc71` | `261ad766bbf7bdb0a269829e7a595d13209b936e93cca5c78c76ba85750987e2` |
| `Representation.Filtration.IrreducibleMultiplicityStatement` | `ce4150389b4d36fd91fc21f36a88e1cff5f946723199431808d0b851a028671d` | `f76527a1f94def2b1329ca7cb7d2bf79a984a71c6b8a32fcbfab69ad8b89cd5d` |
| `Representation.Filtration.IsoTransport` | `95b1edf71a1d6afbf0707d210df6ab5f14976ffa8e418acad3fabd6c15da679d` | `e6ce8defdd9fe71d9f10c976a78cb06aeea3726e69ceb8295ebf837adfe756a4` |
| `Representation.Filtration.JordanHolderComparisonProof` | `6bfe6852fab3a60e4fbafde7c34b0421e7cd8f0c97e4c649e9398aa51eede647` | `e80d9c6de5c0a941f59182ead01204caf88f20fd07916da2111fd9023d100ce0` |
| `Representation.Filtration.JordanHolderProof` | `372a06166f8951d57e18511b454766fe302ce2a18b90ecd226d2d35743445fd8` | `1431908f86ed4bb8821936396161c2a1218e3983f4fa03d3e9134c1fe38fc85c` |
| `Representation.Filtration.JordanHolderStatement` | `4d5ab5d99368fff74399d7b14cdb89991d1e8afe6f9d607ff9224329f05f14be` | `ded29fe841ae79d4b4727c266cfe72a4412c27a55515044597def7da34e88e6e` |
| `Representation.Filtration.JordanHolderTransportProof` | `79133ad26eac0ef1a5511af50c3ad0511d7a95c540a148ea1b9813e9fb845028` | `774b2daaf95042930f4d220e9452ca7fb080bb813753a7fe8d1dff65f9d971c5` |
| `Representation.Filtration.LengthCriterionProof` | `96ad82a58d6a1041fa1d74bf0524b415acdbb43da269514091bdb56431535216` | `34a61e7e6ef38b735b1bdbe35be4601917d9ab2196eb02590278ade27e497c90` |
| `Representation.Filtration.LengthCriterionStatement` | `4f8f634a982c2514d5e484b9274e509a9cb8fbc778b54a80a60deb30628a75b1` | `3d4569cc95c3135efc984a5e3c3a3ab85b7b86cd6d8b1ff8d7c5ad429261fc5c` |
| `Representation.Filtration.LengthTwoMatching` | `a39ced6cea94bcedde5c1ded8b8af5fd038c5627187fd1f0378c90e877ba6565` | `26aaf989c06cd5fa9aab1ace27f51c4a04dcd276649a751f71153e179bcfd8f5` |
| `Representation.Filtration.LengthTwoMatchingStatement` | `40ae1ac47873d518ecef8fe49f8450d224802aa5343415f37b71d2534a000ecb` | `77c882934ea96a9a04501e17d06136a9fbbf50548c4f4be3489e33c7c612d57f` |
| `Representation.Filtration.MultiplicityAdditivityProof` | `c5d215589c6aae8e660b94712e7adaf34f5944cfa3255b48783862c27f3d54af` | `3bb78e337ff8505975b89f6aa07036b30c758bd03fcee0b1d35d621aa0841c49` |
| `Representation.Filtration.MultiplicityAdditivityStatement` | `c277e4aba9529fc951018787cb80b8157f30f60e76fd0ff7e237787ec314d836` | `36110650b8897afcd1056e1b12085cdab0ad09e12620decee33b69d2664eaf9f` |
| `Representation.Filtration.MultiplicityIndependenceProof` | `447e71bbe078e8322f01cce8027f0af0907a0fa003c31e8a777962eb5d275478` | `b0ff8845428cb97363611d671f82d8e8e0d878b982e2751fd8f114b2f5407016` |
| `Representation.Filtration.MultiplicityStatement` | `eee2596c0e71d7a3750a625677c9e6ee5b435a1ff32d4924f755b774406c4ec2` | `183f2aa047781ceb727bd0832b78265c6e486e12c3ead7f3613e9c6ba5af7eeb` |
| `Representation.Filtration.MultiplicityTransportProof` | `e653ba09593db2441cf1ed602cb63478fd0de006194c62a8e76b65314dc95e6f` | `d4e3c58bc76156613cf5e65bf4c057f625dfabb64d5d53b00a1adcccaaedf054` |
| `Representation.Filtration.MultiplicityTransportStatement` | `230b951ed2e364fce1cb8def50c5a1d455892babb722eade7ab1f1f4af38227d` | `ba6b8ea79823a89e2126d0ce0bdde17b730b4554f3cf99a0fd9758082f80f475` |
| `Representation.Filtration.NonzeroHomCommonSubquotientProof` | `ec9fafcd5e5045a00aae8514cd6f115381c10da701c797c2ab569f7d05b945f9` | `c68ca7eb69a9adc2121ada6f97990068588ab4b70b955c6eb10b12d63c7e59df` |
| `Representation.Filtration.NonzeroHomCommonSubquotientStatement` | `b4db80723ad461d3b55093fc132c7905cdcad2c0090c526b55beea9f8cb595fb` | `fc4bc9e0758c2d31f126d7d176349c3c470f069e0634ada76559685489404545` |
| `Representation.Filtration.ObjectDefinitions` | `b9025d1d855ae9ce04fa717d1701da690bf9a3aade05f395ef04dfed5621e397` | `5ade428099a8ae2fadb3dce858928953e3aa854e1d939b18b0e35d4336306f08` |
| `Representation.Filtration.ObjectTransport` | `fc915508e0d5bd576f0ffcbc4a0b822e9cec9166d25413efb1eecdcc2fe6d56e` | `81251c75e50497a7bac9b76807e5c0d5499d6a6ad3eccc8931ac1d2c0f66b1c1` |
| `Representation.Filtration.OneStep` | `45e95cdeb4147bdc99536a3846bfbb8ef5ccf717b8cabf49a30019616135278e` | `f067e22bddafb38c2c58b9ed02151018978e54b9ab325209bda5f08f288bc68f` |
| `Representation.Filtration.Precomposition` | `9c99f0828ad28b8aba0bc8e4cf699938d274da5bb48749d558226ab5652a9a66` | `0ed9da73ec8e691764872191ccb83caaed417febad904b0e0ffb6186814dbbb4` |
| `Representation.Filtration.QuasicuspidalVanishingProof` | `1ed6e286ac5f21a81570059df67f3b6206615e24dd31ec96fe487e4120f35e36` | `4f5dcf95eccfd93d52ba930b71cd2db32e9d15aff1545c966080e9f5549b9c70` |
| `Representation.Filtration.QuotientFirstIso` | `599e8596e54c10d8866ad25fca64aae22a9a2531a721aa75df05348e057c3918` | `7e74cf3f7bfb720c8759f94758d289bf9bb72c4440aff4f7287278710fbb67ca` |
| `Representation.Filtration.QuotientTail` | `37a83df0da91f860f9fea6861c95ac319085ed1a3f3b5197b7bedbd99c764249` | `7252713afe16df0bb3699942da99656a64eac884005943fda98471df77388e99` |
| `Representation.Filtration.RepresentationLength` | `26b3b625e4edb3c80891c927f6e7a7817194a1443fb72a3ac1692d9176ae085d` | `6b4c8c821b8bdc7c2786dc6a275dcce27f45bbb67de2a7a4e69081a15a16670a` |
| `Representation.Filtration.SimpleMapMultiplicityDetectionProof` | `1b3a1e83f89e1604bda44e310087586611f48e8a137ce39e010fc11fbaf4d6ba` | `171237e8d34cd281eb73cf4d239ab2baab94556c27c19b5684658f81f9495cb4` |
| `Representation.Filtration.SimpleMapMultiplicityDetectionStatement` | `27ba5dd33627b94aad82bb50c6c0e897004cf3f26e0e14dc59707828326d454c` | `b994b0cf71cf6a24f5ca5ea2e4d501abf0b45bf3f5e6ed4f0ecb5ea746972ff2` |
| `Representation.Filtration.SimpleSubquotientFactorProof` | `6f50ec4a8554a2646e489c3029a532197b5b40dcffe4a700d58251b6028cfbef` | `3a996046869750ed765b91018ee9d85b2995ba8103e739d9b55a14d4dd031ad6` |
| `Representation.Filtration.SimpleSubquotientFactorStatement` | `1679e4ff4cf1c357ac0fbed089cc9c2f6badf2e46af012c2139d4744ecbe43e7` | `1a670002c0e7e0fe7e0748437fdf53ea6d0e1044d58ac9af12f8320785350fff` |
| `Representation.Filtration.SingleSurvivingGrade` | `02c9327f519bf4928899d11a015cce603c2ae1f09ce6da055f72e2882d459123` | `d704b9a6ef8cb05fa5b230277653d0e326c8c525cf1a90f7e4dd63f9e126e52c` |
| `Representation.Filtration.SingletonIso` | `abf5ddd0423597926acbcf440375760c8aee1d875988c470dfcd97f5d6873566` | `765978bbefde2be641932044922dc65fef8e3238e42d08ed3e0bb47f7b5b8765` |
| `Representation.Filtration.SmoothDualEvaluation` | `683a1517b6176c10871f1231aeaeb9b987d8d20831c3ab5eff54f7b9da5f96f9` | `2a645a2b701937a0059fbb11171b0a52331a9e353bed1a455a10ac98548de77b` |
| `Representation.Filtration.Splicing` | `c4cf2a0cc7dc25aa6517297198e9c715254c5c410bcbac694e4b5895fa939e75` | `efcba65b2baa830b6ee4508bb7b9d8c06b4f549b6233075b404b3f6b14d95482` |
| `Representation.Filtration.Splicing.Basic` | `8d7209b0c2db100bbb861911687c307e74978e748cd2d5f8ccffdd63b3743dbb` | `f2f5fc96dc9ee29e693e9f00ab95940756bfbe1a7f8c73681028df8221820337` |
| `Representation.Filtration.SubquotientAlgebraProof` | `0aa0295d5f644d5227542b744aa07bae6950ccda4bd4e872fdc5dd8dc47a833e` | `13d9024864ca8bfdfb7566212784abd5bf7f80cf2169e42297f2155e2eddce54` |
| `Representation.Filtration.SubquotientAlgebraStatement` | `9156869224eea4947b177cb3b88cd0858364d8d997263ad406ef5218da464cee` | `4caac13701daa326b930ebd856acf939bda978fdf6e9b89784ee502f8633835e` |
| `Representation.Filtration.SubsingletonProof` | `83a42401d08a302431e3b749b6389d9597d6f89b15e20a5cf1e7172b7a6fecb8` | `17e7dc60332436933548c851679c9dac67d5f589ab009e61067d1a0b215ca377` |
| `Representation.Filtration.Transport` | `40879cca9b73cb71376ef58577bef02dba9a1560b0a73a7ae1f94d32fe4cbe13` | `e0b270e2456752d15370f4e92065a915314d0e00784340985f7fd120844140bf` |
| `Representation.Filtration.VanishingStatement` | `ad0a8723be20a364e3f7ccf932787a0c35da7064476eed9e75b013f97ad5ba40` | `a3d348bc35bda4647d75d6e08c7d452e578800319e0a53fc27bc4765d7cb823e` |
| `Representation.Filtration.ZeroFactorDeletionProof` | `ad31958cf67163d755aad477b59778cf4008080f96a953ae22241fda86aebc53` | `40f5d27f0904cdc501b04b50629a2c1be81cde0b5595e869e2acfab4c7d28503` |
| `Representation.Filtration.ZeroFactorDeletionStatement` | `67e18671b041b3e5021ba781011dff10537426e63b14017668293c1a39e19848` | `d8400e4a2c9eb5b739b5d8a936951cae745a9452fe9f451f985100bfe862b07a` |
| `Representation.Geometric.BlockIntersectionSplitting` | `909ede4f951704138c61e4af9beef74f3733152ec0269704b8ccbd139e62d66d` | `7e0e426e31adb8cd2240dbfed50b09f2a6aff51e6e73791ea1866ed592c96dcc` |
| `Representation.Geometric.BlockSixDecomposableProof` | `7e01f2a13ff8ff3b3b7d5d95294555c58ffabdf75f2bb8ee846c9ceb44aa85d0` | `ddb3b7be9fd7db7ac224b2da5d135f075010090041209dc3f4b2fe7256bd1089` |
| `Representation.Geometric.BlockSixDecomposableStatement` | `11f2df75e152074ee6e033c45bdee7771a34783a0062aab5527a0cc1c25671d9` | `a988bc243b3a3949302ca915d0338e797c24556b901da4fc4f7852fd5fa0d243` |
| `Representation.Geometric.BruhatDescent` | `51508f236d4ebb67b2d50bf853ca219a3c5004d2d85961cf1fb696b096c16ec1` | `daae4e710e9c49089663b505626263db70c1deb346cec7bd4a882ea06c019c34` |
| `Representation.Geometric.BruhatMatrixExistenceProof` | `911a6c003d5e801869f10f014644889a144ed9f8aba643cc87acfc10a5e074e3` | `c62d2f05060618c19a61e9a42055af4227f8544387389280f4fc4cf5341d8d4f` |
| `Representation.Geometric.BruhatMatrixStatement` | `c44fa4d8d5d3f3d841c47b461a6d63077bb5dadcd700c2e665726b983d51f4cb` | `bd3da3de41809dc6a27c2292cfaf3a6572627780cec6927b39fa7bc4ae445367` |
| `Representation.Geometric.BruhatWeylReflectionProof` | `f8f1ed8a25e9719d122c25001e6af61cdea262a5db0828bfbbb12cf49c83a8ab` | `ef1be8aedcfc2ea5470a8a4517086d1067b55b00c0110420f068f23afeef6e62` |
| `Representation.Geometric.ClosedSubgroupAssembly` | `e56a8e0681834f21963ad4068ed0cc1d73cc81e7505d78b519a9eef4a9f018f0` | `0a3db6e13fde1ba13ab1af1e3235a62e4c156782dc0ac58dc3b983111212db9e` |
| `Representation.Geometric.ClosedSubgroupDefinitions` | `bc88d60e186b12f0d7df8a3391425b0f3caec3edf7fa5307368a002ba17f581b` | `413e71c2c52105bf949dada453ab9b95f474d8f6e3b54717d942dcda2884546f` |
| `Representation.Geometric.ClosedSubgroupMackeyProof` | `4a5340026226f86018ea1c8fff1649d9fb107eecaaee294bc6043bd6318cfdd6` | `b931a6fa32acfaa6c95ecadf25c42fa725b38e93e2a19733d6ca01748bfecad7` |
| `Representation.Geometric.ClosedSubgroupStatement` | `146d56e0f5bb0465da7ee6ce9daab93684703c5a9fc8fa3d3d450de3e118c60f` | `3f024633abff72ffd7e01fecb254718357c31d17d4dd6255ff9c1d0df8f96b79` |
| `Representation.Geometric.CoarseLeviReversal` | `8c41c871f220ad894e1c59d26af25f37d944e09a4f39012a5119af52e82e2458` | `43190c8bb5182ea67a5fd56da4e0c75718fe636bf63584fe32d6b5787baea289` |
| `Representation.Geometric.CompactOrbitRestriction` | `50f29da3deaa727d85ba696f9ee51cc1c04841b76d64167d98dd5dd7e7bebd80` | `f250ad4700528f6b88d6fa8460ba6937bc47fcb53d770d0671c877a9e148f053` |
| `Representation.Geometric.CompactSmoothComparison` | `68300e0c49d367fe9e030064781c2edd28651ee9d688a30d5e87baeabf35d23d` | `f150c689eee95167df1f8a6570c591dc1d974a7772ceb755623854836eeb9655` |
| `Representation.Geometric.ConditionalAssembly` | `94a663468d44ea0ec1dd5a24fbdffb16b5b35b8a55cbbb13c5f252437120baf6` | `41cd4e239c18503fdc4e6dd85023d4eab4c19806ce46fd13aa837fc3ab69697b` |
| `Representation.Geometric.CorrectionSubgroupCoordinates` | `59a32a99f0447ab722d7067657ceb68326c8da24de5f52e57ae20bbd564b0a06` | `d40df6858c1e8baa784991d833eeffd676bb9ddc309e6156c3338465dfed8ee5` |
| `Representation.Geometric.CorrectionSubgroupDiagonalHaarProof` | `457c83701b1f83d6fc3f7165e3df44b3bb33f5473f0956c8cb8a3d50263e8b13` | `ec568db4d980ac64702b5a74a05bcc94bfdce9fcdaf3029744bca2e6c2f0469b` |
| `Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement` | `bc3c44732f7b7b00e6a362fc0222f1d979d352011d00b370e9ebe104b700bb28` | `2bb1ef905c0c74d22bf07c5308a0ee2858190e6d0f3ec6158837353a89e9be3c` |
| `Representation.Geometric.CosetAction` | `291f5639f837f3840b6f985443960017d900a4148aee1ca6e35d14ecb336df3d` | `e50b89667570d2529373a2df2d2ddf4ac94e8bfafc74328b9d2dfe32d7475ec8` |
| `Representation.Geometric.CosetOrbitHomeomorph` | `7974b00fb4380eecfeb3e45dfd4cd0be82431e35f4c09c54fefcbed89e27ea8d` | `900dff8598b4a2d7f0352e5963121ee6c7329c10236ac2a14fb3995478e40347` |
| `Representation.Geometric.CosetOrbitOrdering` | `380fe8b521cea12ab27183a17e10d70c1523066cd93e7ad9e1635d80c7f47399` | `d74b006fc310d10f7a020e0f86f0ad76d8d0fe3f5c2b2f0092eb80012f055cfa` |
| `Representation.Geometric.FlattenedLevi` | `6109a5efa53a097a77684bf9711711d057a8d80788952deb71247f9abcc3256b` | `5062bd35a0a1d63d4fd68dbc9ba5270445955e0e39a3d014f34a53b27ff71c2a` |
| `Representation.Geometric.GeneralCorrectionCharacters` | `d54e99814f0f4aed63316eec6b9969141ef9b208aecbe4b2cd26eb9a32632b75` | `e12786591193dbea2c9b3fd40a5e6cb5e8394aca20e85e6cec1b79ea5df9c8f0` |
| `Representation.Geometric.GeneralIntersectionNormalizers` | `a5ab2bb3fbd4e4e98543520dbaeec860704c0b158fb71e34e4cdf2197d4b1bae` | `6d30bdd8f7e7f88eb227ce9cd231d8dcd88e339073401df509c84ed70c7487a0` |
| `Representation.Geometric.GeneralIntersections` | `84defeaef2593b58429fa9a9eb9948050045df8d76373fd36ff60ab66152a707` | `a0bb4adb01beb709455d654cba473a264dae1e1bc0370ee18cad49a697201b2c` |
| `Representation.Geometric.GeometricLemmaProof` | `e0a3d644366c6f811593b3b9e5c08cfd94d22bfa3f9fd79d509aca099db6715b` | `cb0df25c575e6a26576a71589ed7cc73820a44429f364b0cee9a09ed953669dd` |
| `Representation.Geometric.GeometricLemmaStatement` | `2f7942617b88947db2150b7ffacefd6b34267340d872995f29aeab8b79b5d58a` | `bacedb9cc0dbbb40b34b948d82af91117d7413c822c27f0a5d11c03320591eb9` |
| `Representation.Geometric.IntersectionLeviDiagonalCharacterProof` | `2d0fa90e296c54095152f4c582c7ce4cc6ec9215363961324612aef8f6f4a384` | `4613cc4f5ea1b667f7954f6881b4f296291e87478bd8bfe7fa118a8ff6e10fe4` |
| `Representation.Geometric.IntersectionLeviDiagonalCharacterStatement` | `6746a523bd21bf0825a1659aa4dff4ba4968eeed774cd44e2dffccae5005fc78` | `ec2b1c9898fb64a1f50dc45b7087f1a9a8bf8436e751d4cee32e6919c59c8d78` |
| `Representation.Geometric.IntersectionLeviModulusBalance` | `c9a1eb4356596ab650222722ba07f252ad3827e4d01edb354c8f3e67bcab165a` | `79b17544fc18af513d6e1764f8f9a57e5648abf6f7d5096dcccfe37186ccf56c` |
| `Representation.Geometric.IntersectionTransport` | `df9bf7cc81cbae05eb2e4b6b582ce0bad13ae9f983b4d7c7fad8362179b733fa` | `950fe68d7ac04919a28d7bf936e20bc6237e61e7db1e1ddc6acb262c550de2c2` |
| `Representation.Geometric.MonotoneBlocksProof` | `c8abbd6212fa4044fe9d8c2f5004f599ff108aa35e2eb5c9b21c6c83d1ed62f4` | `35bac664c5ac96a59293d3bd1cc5fb0ef719fa00f00955a250511323614ab120` |
| `Representation.Geometric.MonotoneBlocksStatement` | `17d396091cae946931dabf0137528b88ff38f1b083ba2d793ac49f81d5897b0f` | `c51a7bc6f06fc0189944a1fd02682638eb487b76f811dc2730b78b999300e9a4` |
| `Representation.Geometric.OrbitRepresentatives` | `4f55d054b8417373431980f64d7e20cf2c6e9084bbd64e3a87efd449d8419857` | `99e81305a7bac84e19a5873e35c1ffdeb70094c450139b390ae944a2eb8dd2d2` |
| `Representation.Geometric.OrbitRestriction` | `646b23b4c9c8b069044fce5182e152f86f6ad6f53d4b987c061e2132a35f80c3` | `0ae961fd6ad53fdda7e32e2024429351a3224fac2153f6e292e8a03112db17df` |
| `Representation.Geometric.OrbitSectionExtensionProof` | `39f76a02d2c60259db0ea2212699ca078c89955945dc2f663bddd21ad7d4cd2c` | `5b38b729a25111d4075ffcae0a73b2f8379022239f6b246b39b3c2181b1774e7` |
| `Representation.Geometric.OrbitSectionExtensionStatement` | `d2af475d3a3159c6120c38e510047d8dc7130011e46016bdc875f821492e03b6` | `6915acf554e86fc4498d2b9dada87c5907b1c67408aa9f96dbb9381397ab9213` |
| `Representation.Geometric.PadicCorrectionCancellationProof` | `833cfa6434c6dc66eac868d7eaa225ec4fb01de0b9d968d273b6035e3586f3f6` | `c6b15e0dc3c352bf1dd345916b7f053cff7b87256a73edaad8c7f98f20d6067d` |
| `Representation.Geometric.PadicCorrectionCancellationStatement` | `d16823421ae78cd8bd6c29d762365f52b3431916a25d7f534633865c68845073` | `b76818f13dc7a1d404d0c327383ecb7d03c40918b53d58808abc7b4d1f05aadb` |
| `Representation.Geometric.PadicParabolicBruhatProof` | `8a712112dc65d19e37325b85fbfb9dfc33a850a4bfe7f50f8882a1a57d17b769` | `5e48ae18b5bfcbb89690e6f2ab3a3eb41020e0817f5318a39b4f6106efb247de` |
| `Representation.Geometric.ParabolicOrbitCoefficientComparison` | `72add67906100703df10b1edb4ce91f569b8017ae85a9721b44b624d5127a99e` | `c26150430e54121bb9abf04da548d03f45898620dea28b0fb3a1f8292bcca278` |
| `Representation.Geometric.ParabolicOrbitCompactComparison` | `497b3df76365c3200f8db8dd0269ea1a3e435765ceec1448fe4778ece4fc9389` | `c1daf34aa15d5315629012f920fe56650dd17bfdcd1638f1f493a3d31b2035b4` |
| `Representation.Geometric.ParabolicOrbitComparisonData` | `9c2d40c23db729f30bc8b2e373917757cd0c355f891f28c546b5e20a7d2b5341` | `77a4fe3655d8d3bad88f42ab309c55eb991706790a36b33a4725237d1dc16529` |
| `Representation.Geometric.ParabolicOrbitHaarComparison` | `a7ef330fa1fc4e6d80d7d298b07ea333f5658d2ea4bb985a41a2bf739501ba26` | `d2daa8e05b950423cf37a3eb1fe1ddd97fbe87c711b5a280f84c0e70f7b38398` |
| `Representation.Geometric.ParabolicOrbitHaarRatio` | `cb17e84554d894e7fec745a082dbdbc59771a7817b932a356b0f022ba5bd4445` | `9a80540f1543231ad62562e4e862fde5f5acd02232010f30e0a0810f4c98d129` |
| `Representation.Geometric.ParabolicOrbitHaarTransport` | `18ce654dccf567fafa0c15818b892a4b821c92bdc3832385dfb20fddd740ba0c` | `f6a99fbe3387618c14e6cf63e04517dabd6676597d775085dd341d5e2d7e7082` |
| `Representation.Geometric.ParabolicOrbitInductionTransport` | `c1be61c13ab56ae5c4eccca242683c3050d2119dbe33e1c72c5d0851b12cfacc` | `f483246ba064f8f4bc7fff0b594d25fed55b2c760cd5db5c7106040b0db02ccc` |
| `Representation.Geometric.ParabolicOrbitJacquet` | `36877041f011dce498a95eb55d544565297376f03d4e93e2c49f6a3f2e826c8d` | `10eb54237761b6b6257b975b31fb21d9175021645bc7afb7ef48888e7e329b83` |
| `Representation.Geometric.ParabolicOrbitJacquetProof` | `c147d63559143418b76b641136edc33b3a28c30c6dce707b09ef46a4d87dff9f` | `04f55b6ebabf47ac1897a7b9e9e0dca46c96e9a7de06b60c9a6133c2ed3e3ecc` |
| `Representation.Geometric.ParabolicOrbitJacquetStatement` | `db2ef3b82334368b99b52fe41dec98f95aac61135ffb1fb2256a29fc46c15e2f` | `13ff5a89be936ea72a2f1c343acd34c14bf97a22eb043a1a7f28eadb8fb4be4e` |
| `Representation.Geometric.ParabolicOrbitMeasureData` | `f92495f45f4f45297994d1eb407acd326dc2d3649aa88ff6730dbe7971d9f551` | `d633aa8907db00f2906b03d3d7f5f8a862cb43cc928a7801f541bb814f6653a9` |
| `Representation.Geometric.ParabolicOrbitNestedAction` | `472097424d7ef6ae4bd11921a5e0ff3efbbf70773ed40ed548cd9872310ac87f` | `c7a452ed82870a5489610adcb32bbde2ff13dea9134074043cad2c7bc8342eb4` |
| `Representation.Geometric.ParabolicOrbitNormalization` | `1199834e3d79cafefa531102522c1c07b51c655f10869313475e7515d9bc535a` | `366f5bff9345b04f5fc6f9e91b8b9b5cdfd4f28828262bc83e6444c6b67a306b` |
| `Representation.Geometric.ParabolicOrbitNormalizedCoefficient` | `6a9175aaebe092bb9684c45aaa16eb1d3df263ac14a8ebeb4f03a4c634f72853` | `e20b73906db5bfce2b249bb96cb4d07500d8287e55ed131004d71a73e349f35b` |
| `Representation.Geometric.ParabolicOrbitSectionComparison` | `acfef954307e8bb758a001ae2ea33e0551e4f94d1dbf2656a8cd726e40ecc8a2` | `e7b5aa62d923ddb5ee1a207e8c78fe57abab3774bfed9d0af7a68fa5ef634ed7` |
| `Representation.Geometric.ParabolicOrbitStagesCoefficient` | `91e08900227a9294878bb1352c4f92368d1cb11d8969893675613ec40bbf1620` | `bc04f73ae78c7578ce6d0afa0d818db9e002bd4d7f50d71bd7831d8d80240d6f` |
| `Representation.Geometric.ParabolicSupportFiltration` | `ee59b41fd2cf0c01948ff974ff72da3023e2cc9a928d06e43681ed5537a869d7` | `3386329be5feba127c6e96381355af5ade2183f870fa5c663fab6010f762eab3` |
| `Representation.Geometric.ParabolicSupportGradedProof` | `fe04ced955542355e1029d1ccf81ffc12d69e0b76c84fadd54e6a81345a68194` | `6d9d370dbdedb3fa5d8f2555fb8f4da82e43acd4f06891786bb68179f579fd04` |
| `Representation.Geometric.ParabolicSupportGradedStatement` | `c3f0750429132184d6e8fa18e7b29279b2ec1b7879b2b4d3542be4eaafbe1c5e` | `4d365f8f55ac1f104f707a3464ad1b3750cf5c9b7fc73dcb26f9a73d9c46c45f` |
| `Representation.Geometric.ParabolicSupportJacquetProof` | `4ce172280800b516e24f6fe8985808187e8036d80d0599c1e04aaf83c92a127f` | `f3ee70d6809ceb05e6fc4ce41911ef7b99e25223203ff1ad8f2851798709bc56` |
| `Representation.Geometric.ParabolicSupportJacquetStatement` | `ac9ef9642e42c8d0c7ef9fcbebfd70fbf51d98168dc1ca60b246bd4c47d48ee9` | `7815e31baf5ff3796a03e35cd88b226c6f12ee5df6edcdc0674fac957b1bce6a` |
| `Representation.Geometric.ParabolicSupportTransport` | `32db4e675b7594bb5890eaf0d017a5713a11035106816de7e6aed8089c492240` | `316318464665108dda333b61915eed4cea3ffb920fd421849f4ec0b041ff0823` |
| `Representation.Geometric.RefinedPositiveCharacter` | `b02664bf1534b59ce805b1376d5a4f6bf5ac1af68211d4d7b629750764e82752` | `594e14dcf53cf31743983935e3d8b390c2c070b2068828328ecfa5a92ded2b3c` |
| `Representation.Geometric.RefinementDefinitions` | `774e0157847992c2d04e366503befdc911795979843e5cd1136cfa7f6cd969fc` | `ff8eae8381454b873578651ffbf14a5d75bfcb46e1bab709a20124d024706a98` |
| `Representation.Geometric.RefinementFunctors` | `c9d92272a967aa5db712806ce13eb5ce573bf78425242ec190a3250902841b9b` | `378cc7a52950452db9e9b4647cb8da8612d8275afe8a4446541208196e4787a8` |
| `Representation.Geometric.RefinementUniqueness` | `3e52477ec7301188b478f42fe8aa93d0915d793b143861d25c85e78c4566c990` | `5894a7726cc2696ea2e5970568fa6c0df46c4a8df12ec01caaac65d6cdc9b76c` |
| `Representation.Geometric.SmoothSupportFiltration` | `7416224f30277a46651d787e6995f2c46c9c0f42d54ef7b4c70a1ed7e27fe4c2` | `8c2f1546925241ae0d005881d242a5451b402c5db618f07667848ced1e2c9e31` |
| `Representation.Geometric.StandardIntersectionsProof` | `5047699f2bcc1fa5f701cf025dfb3ff068bd1d9221a1b3311c8e2a3b109917d3` | `1cb06df753f4187a70fec9e9eca3101a830c0b6f3024c6c505a13ce8ec04469e` |
| `Representation.Geometric.WeylDefinitions` | `5f71ddd64c10ba33884b1b1ab684443ec650192a73b77bd487011fdadf138d01` | `979ea6916e2fb3c7ebb427e9954719472602cb84de027ac9338b22df95e74513` |
| `Representation.Geometric.WeylMinimalRepresentativeProof` | `f96bdf633e416a62adc0c76fd8335b810582501c2d17f1534d34fffb5e951016` | `2e1e7e7fcc2df036c42e86886a2490687c2bd03f86700d6030ab17e76f904aa2` |
| `Representation.Geometric.WeylStatement` | `45d7e698c59e2b04a100dabbc296abcf8bb7c49bd84b669fbe3dec2e8d298389` | `79b776c818b8c27e5285e5cfc2a24dea5ae2fcf1cdd3355ab20fab18cc8366ef` |
| `Representation.Geometric.WeylUniquenessProof` | `7a191b6d715d6609674a68f4e8a4e04b09add65762b0e25472a3467db8f99be2` | `912309d9d0985b3a8c08311f6c397a22db3c4dd09d97bc90ad04eafeadb3321b` |
| `Representation.Geometric.WeylUniquenessStatement` | `f762a4e7ed5d1b38a5ed16f3a5a97bbc264514549046e3f9f5fffd96e5d1a185` | `dfd00e8bdbf3df2e77872ee6fd2594da9cd9e1d0f13a8a678406647411c505ed` |
| `Representation.Hecke.ActionIntegrand` | `9367816cbbe6f33dfb6da7fdbbb80cc22acef8577713fce31ea721e6f8efcdc4` | `085d109b8a96021c86ea780eb743985bd6f4c4e0aa66f5d1e25f2bc75f34bb4f` |
| `Representation.Hecke.ActionLocalUnits` | `b88b35c07a63ed338125842bddc1ffb2cad74c5cebcefb9e1a60ace2d84ed986` | `ce318a98199eb3de6e00fdac12edc8e7b8f4188ac47da5c0341d9bf404b3c35a` |
| `Representation.Hecke.ActionProjection` | `337746f35eda7a58ec841b0c7d4393924d4a6d4427372ae0f3c2a992c91f1379` | `fc69f750676c88e4629b4ad6412bdea745d0756bf2ba25963c9e33a08f866a64` |
| `Representation.Hecke.AntiPullback` | `59f6cea930875893dbe80e6b2d72b416474092f04e3199f026c424e29f045fd7` | `11aa64c29962fe7c58f583c9542f5cef530c6a5c8426c220a830bed5cdf1b4fc` |
| `Representation.Hecke.CommonInvarianceProof` | `de283120e8f845b419d4643808f13a7ade57861ff9c9ca275f6bd1aae93ded40` | `d23940f731f95f445085b22ca13f7fc55982daea753e6ee667a335e2a382b7e8` |
| `Representation.Hecke.CommonInvarianceStatement` | `9edcb9b9f0444a767a4405c316ebe2d5c664472b1abc8a840d37404c65ac4e8e` | `64874a7979ea60ec9dbcbe4980d6f444f19645cf17eca8bd533f8516270253dc` |
| `Representation.Hecke.Convolution` | `7aed8c839a537413ca951a719f8bed7eeb51e7faa1693efcaeb630ee34e96832` | `f3a9ad1ad3bc612d966e78709cea8717bb8dceab05e290cb20ebb1a93a9a033f` |
| `Representation.Hecke.Corner` | `580ae8915d85290c27b239267190ca71b5f6f4eee73fe628cfda188bda43d310` | `7fda606ba78735810be037645b3ac02cb01cd7b3148865a927f5b8e47fdb94ba` |
| `Representation.Hecke.CornerAction` | `fa548385a520e3a0275149c05de158ba1dce5ecff4187ef5ab4243ab8e704d7e` | `6c3097d43a40467697ec00160cf8dbfe9d197db5aace79767cf255d84a29cf0c` |
| `Representation.Hecke.CornerDetermination` | `a40f8a074cd2c3476012fada6210bf7726f2932a5ef18170ee0d34d919f32676` | `397e0bf625c171d74703cb920d860b985df9a47c8d7dd5fa05d158ceda148e1c` |
| `Representation.Hecke.DoubleCoset` | `b1116fe196b1187c0f057520a6f8481e369368a58c25be415035049db2638567` | `ee18f44ae93d782916d6dd9e33584270f98160c5648c50fc77bb04c771bf1de3` |
| `Representation.Hecke.DoubleCosetSandwich` | `8d37cf325dd1672e961c6a5880088eebd66092c3ed0005fe6c2ec75e91e909c3` | `1186d00c93031ac47e4227e80da0a79fdc8ee2e85f0a58cf2d1baa816d8d4f7b` |
| `Representation.Hecke.FiniteRankAction` | `9159f45becaa02ca35b37069f7cca558ff855cbab563aaa6f628576f679bdb7a` | `ab593d37427aaab15c078df2ca9baa23a917dc0f10edbcc7eb44cf7431d8f3f6` |
| `Representation.Hecke.IntegratedAction` | `b799b6315116b6ecf08c785539e173976c02374546327acb298379b1a3688d42` | `48b1849e0b3ad07167f538778aa4a9fed994c1abddfe31dcd64af08bad54be10` |
| `Representation.Hecke.IntegratedConvolution` | `3c7e7490beb25e28220475b3a65bb8184c7ba3a7e44c61a12c2d1ebed6f97b5a` | `d5405d9c03b85b8ad53dabbab65a7c768bb9cd25663ff679e7b0b8e829ea027c` |
| `Representation.Hecke.NormalizedIndicator` | `5521284b4f58343762cf7180ecc2402432868c7a4ad21c7dfd749fa0d87be9c1` | `21d8edf9d8e7684d087e49cd36f061dc0aec4092cd9493711e76bce9b53d02ba` |
| `Representation.Hecke.SmoothTranspose` | `cf2c4affde713bc9eaf109975a25edacedb33e7b95a1ebda6c4e6875c920eb5c` | `21d3adad47c3ccc40bb3aa9aa2cfd7a83dfeb0e3ccab830f006c138c6cec5694` |
| `Representation.Hecke.TestFunction` | `57db020a996e2486945c92dde4073fd13a5c94201b8184d441d51db417708749` | `5d615c6b041939d68fb4aaca47b09fbf365f06453e2d7e3015e67f96b17ea5a3` |
| `Representation.Induction.BinaryPositiveCompact` | `ce69ecd118c400a5ee996f2b9d0aeb529165eeffe78a5c548f2ae722fd6e81cd` | `e70a0aa4d78a98de34b727a37e1969d5336ea4bcff14ab32678692e334418c82` |
| `Representation.Induction.BinaryProduct` | `7b202b649093a2a7c19a3b1e805c8e6c061b08050d6c589d09660306ee20a92e` | `6ab291b2549a52cda5081e691532755b350c4e81a9e7c9aadb2f85ef9efa8e5b` |
| `Representation.Induction.BlockCharacterAbsorption` | `148f20d7bca02c47c390cd59b65a3622cb66895be46bb1c9da4b7845723577fc` | `c9d9ad8e516163fc45655704894e0fd115147234625bee4685aea92378ca32b5` |
| `Representation.Induction.BlockEquivalence` | `820354c617304b6868d6bb543252587639f1e7104dc1a55c6e0695d9afea70e3` | `ac11d1f2a8911d8ca7607005d0c561c3ed1503cecd2e55c8bc190c7caaac6184` |
| `Representation.Induction.BlockFactors` | `734929d120a12fd858919ec95661922a65435f9dcbcf2deacbcdb7ba4973aa00` | `fb4581ce31a1ecb8b4a0e9c1b715a53e3a71cd74b710114b25b802177d4dfaa4` |
| `Representation.Induction.CharacterTwistProof` | `e3e1278809b67dafd0ebdee0a61165b8ff6c62b18f30ef06b29d96bbad648d41` | `de6ae3298eec6be343602cd602eee2803705601ff91740e8f7803ca72b64b8f0` |
| `Representation.Induction.CompactAutomorphism` | `3b1c45374551aed0e43d73c79caf1bec250091278c10c7729ff59bab7de9509c` | `a14aa0a625616c8f2ab867be3f1045973157cd9487bda5901741abe86876c0e3` |
| `Representation.Induction.CompactAutomorphismIntegralProof` | `5cbafe03d6fb679f48dd91a27aed3067a876fcb5764ba4f7a2c1bd71da27b97b` | `51bdae8de1b8e84622fbd1b4a5a61558d68813b74955d51c6319ed4102238043` |
| `Representation.Induction.CompactAutomorphismIntegralStatement` | `a8258c68a788355a7348f2c2d2c644db7c1538e170ed36b12c23e7b9eb6dae32` | `7cd282aa57f005a7f6685c8493e2a5bc342fe2068753e0499ecfe6589254f0a8` |
| `Representation.Induction.CompactBilinearPairing` | `c34a3e11e9fca921915b00c3c9e9fa512554d5e5644855932bdc37f8b55c5d6c` | `e9934fa6b91481c697ca54f012a137f9c7040ecfaa38406d83b21936710005ea` |
| `Representation.Induction.CompactCoinvariantBijectivityProof` | `0bdecfce23739caf7cc0dd4516a189ae5f2eda46b7f07904826dc3afc9acc7b1` | `8d96a5eea21880dfbb5b1b0f6fcb9853bb2ef288a5314b9c5f1b178b6365ca4e` |
| `Representation.Induction.CompactCoinvariantBijectivityStatement` | `04abbbe07f89a1c2f1195158c55fb82cc54edbd982404f8cfff2e19f704d4909` | `d29bea650695a58bbbff4589eb3ea4dcb701a2d59fe9f2c2036c27da94c9434c` |
| `Representation.Induction.CompactCoinvariantIntegral` | `28239fe6fa2cd58b52a9f42ae97900719bebc05b329fdf7d20342c6874d1b651` | `d16934f58ec05057839e9e0be596be7e9092ff4b8dced1944ec198348bc22c20` |
| `Representation.Induction.CompactCoinvariantLocalInverseProof` | `8b6004b93dc6bd828d642689f40b0af80021fd3b68d9d94866fce2291e174ef1` | `584f63103f811524839a67dc5a3e34b7e687b6bb44ef8ae501881233b106cefe` |
| `Representation.Induction.CompactCoinvariantLocalInverseStatement` | `81ed503d55d48eaee300c98310a4be4fb2e549452af027145c7e457a1849e673` | `6d9087fe1e9178439def2bf7b10e59736df04d852565f206d90e055275720014` |
| `Representation.Induction.CompactIntegralForm` | `4dc5dbf5d66ed48903bb609b75a4ae8072d76f2ebafea782eef1cbaa9e1ef497` | `6e5f23711ecda1c4d7b1ef7a71c5f9ce29683f6cbfff62ef4d7cb85670acf450` |
| `Representation.Induction.CompactLocalSection` | `2a8bda728c8ded860050dd8c8c9b8ccb9524c8e4fe9f5f4a02373be5cd903747` | `99a8e7a081c1628ab63e4b37cda055ebaa12e65612f78ebe16836e6cbe56dc89` |
| `Representation.Induction.CompactLocalSectionSpanningProof` | `34e7edf99b23fe04bc492f08642a975e21210fcf35898cf4a8865a177af68b2a` | `a2ff6cc4bd28a14d6ccaf302278575219c4630188046a737136193acc1f9c67b` |
| `Representation.Induction.CompactLocalSectionSpanningStatement` | `f9eb55515c610df95c1f7dd3335b6b30745c93d16f0a1115d0430c8631b90c44` | `94872567bf8bdf53770c9be9532c17ef7bbcaed03101199ece56b95d8695968e` |
| `Representation.Induction.CompactLocallyConstant` | `a94955a867bf1f7452e9357da122fb25145b266d6a93a96497ee96824f229d88` | `3f14fc07907ddf8c128b741c871efb6dbfd551564fe1df5b0f7191d4a0c65d8e` |
| `Representation.Induction.CompactPairingDuality` | `7bd640faa46c4342cac2bd521d23e85f6987b4218301cce37d7de0c0c9a3ffac` | `e11ba228d78ad0758ff7fd9d5f6b5f282a94fe0f108ca03ea192248aca4852a3` |
| `Representation.Induction.CompactQuotientCutoff` | `92764f305d65cebaf7ae4dd4828f9d07cc20046436cf8beabd7840be2b893d10` | `a6e0b64d8b9660abc3e7f9d12bf94dfe5a76a7090ab32ecf45e34fe01d1e032b` |
| `Representation.Induction.CompactQuotientProof` | `fc60f8cfac2022bc4b7796bc624c3d171fb7e9a6f410befe0082d00a0d0abf30` | `e187c66eb2a15a6167dcbb33265ee6da6d654a879338fc162777eb65f85c1cfc` |
| `Representation.Induction.CompactScalarProof` | `2e5dde1e6aa0ed1959e5bdd6b533ceb7014b01110ed779875d56fd5410ba76e9` | `ceed11fbff7e53694d479c07957f639e68580ba18baa0d5207606a3d825fe1e0` |
| `Representation.Induction.CompactScalarStatement` | `fd4be35392bb9fe32c0af81a7474a2c7fa1187d3a8c143a8c0f3ed9c1383df60` | `b867f459d6df8e5cafbd5632b086a188373e6cc8e760d59cb3192ed0d451208c` |
| `Representation.Induction.CompactSurjectivityProof` | `6cca6c427e31975c0440d615a83484e8a2cca353f23733781f0fa85382497a2b` | `d2015b17c6a6c1ae3728ec4a19c8c71ea309d37d3ec8167b2310e0aa3bfa4bc6` |
| `Representation.Induction.CompactSurjectivityStatement` | `224df72a3701ed3e208752cbb30a36aa9c80c77311046e2384c79d7c3937b525` | `65d4483bb53c587f34a03cef738fe8c32eb193ee6dbeca11bf9ba032023b0829` |
| `Representation.Induction.CompactTransitivityProof` | `404a3c9497f5c6ebdb190bc4c845f818aebdea835c1343329eeb63cf96ad9f3c` | `6f878d5ae1341fb0355f15d1efa7d3136dc506740492be57f4463c7aa5c3166f` |
| `Representation.Induction.CompactTransitivityStatement` | `5f3d0e9591da3e0399df594b07ef4a269411f797ecce8e7355a77c7451dadca7` | `b433a5f7c6c07a6f71f373f7cc0539efcf1bda87edbd14463872f99a365d38bb` |
| `Representation.Induction.ConjugateParabolic` | `ff611d42d41d99a68004ef6ae2cd71ce7167ae45601cd3e1f5a6677e4dd926e9` | `5e91cd470d109b88aa7939d6bf13520f1b291387f6fbac3a8b5072b708249206` |
| `Representation.Induction.CovariantRescaling` | `1bc9eb6f0737fa56cc70134e6a9c3a6cbd6dc199b1243fc67c9653494e894456` | `a5f128298b8158aff0b0ae76f95cce1b346fc473646c61024eab515b1feac56c` |
| `Representation.Induction.Definitions` | `2bfd525fc54bddbd0115633939913789b3ce3c94ba8c3d10187fd01ab8ade102` | `9a794112b9bdd0430d380f29601621c8091e2801674b3ae97fa81601447cf898` |
| `Representation.Induction.EmptyProductUnit` | `1140c75eb58144b858e486908499276864161fc8d7ebc1c8e9ed5941d916b957` | `fe3e25c4ce521cc1c3ea8495e8a8a33ba51fe6db9bf90501354014c5ca732e63` |
| `Representation.Induction.Equivalences` | `b6e375371bdb35e8479c8a160b1658c4fb44b505573c1f5c39d8784b9ae98022` | `69f7526357fe56481b843877afaba2ebcc8f5d9775f4940b1518f36dd74c2d9c` |
| `Representation.Induction.FiniteProductTensor` | `25d1d8de7d89147c35853f9b59e919dc6888976bec5523d88ede83000f8e87a4` | `8cfa42beed0a339517bcb5f12bdf510c18404366e3513dedd73e346ea209a074` |
| `Representation.Induction.FiniteProductTensorBijectiveProof` | `1d55996df73fac5d3efdd7bef6ea1b6a27e5a5f30a82bb1d4ef45b3cdae0a149` | `3c179eaff227b7c2b986f517407186ccba66337dafcdcd760106f5768ad4f213` |
| `Representation.Induction.FiniteProductTensorBijectiveStatement` | `f5a09d68e2854f715efe6b55b96db418a955cb50cc01aefd2916f4c7d85e3e7a` | `5744d6faa3022f32e5044107e4ffcbca2ea6e6e6c496f94f336f97fb34014d65` |
| `Representation.Induction.HeterogeneousConstruction` | `99ddea6e4dbab76d9ee667edc52a7b85edee5f1f5519b3a9e1f8da9726aa8e75` | `7a16abe8dcd20d2fdfad9c6a10c77e3c9215dc2dc3ae97653347c194c82a4e03` |
| `Representation.Induction.HeterogeneousPairs` | `6bcf484ddf0b6e334afc707180782a1bc4a0546f890fa7ee43fa54060e5abe04` | `dcc35b90950233686aeffb8185ca1474a7bde0dd98d9317c1d15ccc93984dd73` |
| `Representation.Induction.InverseTranspose` | `d53f875f4cb84d09b1a638a3b8e111715493fede6e4cd2ac25ffb7301c62622e` | `2691e51553dafca22dc4dcd377beec4bdea28c5b42e2608b0188c25a2210ee74` |
| `Representation.Induction.NormalCoinvariantKernelProof` | `5526c2414ba045386d7d1e65ba83403b179b639e68f4cb43dac9c2921f865ef6` | `5b41c078037d07ef8d9f3b6b0824d06fe5112231a5e1dc33adee316f7ac78c43` |
| `Representation.Induction.NormalCoinvariantKernelStatement` | `c811cab396e838a417d485078731575cde5eb9654aa6b06469718132974980ad` | `fc92226d5279df3dc2405216643ab783b1e3943d9f805ab21c644ba0a7fa321c` |
| `Representation.Induction.NormalCoinvariantMap` | `936af345f2db6c7b6161c59f9beb52af399c2667ecb11f6331d0ea15bc24b587` | `2202645f6eea3476743900a55b9ff32f537a4a0181e9e82b2fa29247eeb732cd` |
| `Representation.Induction.NormalCoinvariantProof` | `48337194824c5ef2d778f4959e65fe38a0bd32b0703cd46f796ba63243db57d8` | `1339c2e8984b4d1754946aef579488c7a32bb927e8c70e802040a0cbf0223d4e` |
| `Representation.Induction.NormalCoinvariantStatement` | `e201821fdeb88d3a554c8d5361c5f52e4958f1972e7568baf0ab4a651187cf65` | `c0c5ccba93201fa0bb721a89924126cedadbaabdc78bee922e0a1eee269d1316` |
| `Representation.Induction.NormalSplitComparison` | `c84f949685aedb4d2ece4d8a2804fa5fd5e2c187e12c9cb77abce89893a91a2d` | `d4b6380ba2a9203ab48bfbb43b2808bb8ad265585ce6de4cf4f2b0a85717d0e2` |
| `Representation.Induction.NormalizedIntegralForm` | `d56bf46ee876765891a1b4265cf3e9bbb3db73ba33fe3b3cf2d3b504c969d999` | `8dcc804eee50c911772b5b8c285ac47e2fe6a4ce4be1475ea3ade9f11d292f94` |
| `Representation.Induction.OppositeParabolic` | `2de8f8ee20c29e4d0a2973ed5e3e0e428b6f3cd206a3a21e0a8ecd8a09f120af` | `59c6ea7fd36546f10a13a0a49826e41c62b96c1d82f81458d4fbde567f4bcc1e` |
| `Representation.Induction.OppositeProductReversalProof` | `57dc558669b05441d7f6cac7b9543b8418369f5745427eca6c100a88a0943ca6` | `f953d878ad6b24e45d064ae1877f86f36a3f9d57b576197259109f63a2010e8e` |
| `Representation.Induction.OppositeProductReversalStatement` | `d9fdb35495916919903219ea8d67fb2fcb2b0185e75b12fdc35863d35bd302f0` | `8197bce9c94f1939358e5d44aa4c3f982cc1ee75cd0e7985b814695ed2eac7f1` |
| `Representation.Induction.Parabolic` | `5cc1602e1103ccf3944cab5a4091717c279c0aeb0cc4252ae3a92bc02614d1a9` | `70d976f7e40e4fa0ac8011184f29544225516ee559b5977f0dc369ac6b8407f3` |
| `Representation.Induction.PiScalarIntegral` | `8fce065de249bd638978e5afda9c1ee5d6801a9520858c951a2122382819b139` | `110a51c33267878c225166fceeb0052fea99d6f1649f0d26af96389dcf76bc47` |
| `Representation.Induction.SingleBlock` | `64bdcc435e7a59d484cfdbf11b5d5b288e11bf793818214bed0bfd2cdfd8174b` | `d40ae490990ae032e2e03fdef35303a406bf1db0e9cac18a81590417318be293` |
| `Representation.Induction.SplitKernelCharacter` | `60b67b4cc12ec53caaa3f818f7ca441e65cac4bf8917e674bbe3728b25447928` | `7b9811c2ab7ba1f497201dd1098c9112416c5c63be0b57cb1698bf5223961863` |
| `Representation.Induction.SplitKernelCharacterExtension` | `3a8ba6494ff107ff3121ab5af9ba1c654fd50e72f16bbdbafe637fa297e53c2f` | `78d48b4494ff7f1426917d47ab96183e436f1210de2d82f764f31fc6f3612ae3` |
| `Representation.Induction.SplitKernelCompact` | `5b62d589130b1b9c662d1ee302233a7ec4475edbdfdd8b1f1a5a3af989367ad4` | `23eeba23a160ce35bad93e83d1fa7505ae254e55a22c1be0fb99b7b529a3e191` |
| `Representation.Induction.SplitKernelCovariance` | `fa55f773d8e8450c5de3d9fb7203d4135739bbbaccb70266e0cac528da1e4888` | `260ed5cba699b33d79e6e383d7eb05d3d6dbbf16f68640cbe37ef225478f809c` |
| `Representation.Induction.SplitKernelEquivariant` | `3d4fd8bb71cfabe7cffcc3b2aa115b63f89ef258b59a1da3f4c1b7e78061ce4d` | `f391b3c6ec9b3772874a39f4fd1c753f96536e6ac00d2d3ea0e8b000cac14b22` |
| `Representation.Induction.SplitKernelHaarTrivial` | `9ce3e3fe82c7d47f987334a46e2f8fbba1d5d5cab991e3e931ea6a9686dba821` | `5241898c8018fba167f750350bdaa94218d837a742ff184d4386bdace8faf967` |
| `Representation.Induction.SplitKernelIntegral` | `2cc4eb6ad2de3f4ce020bf2c891d5859593fce46476530f88ac3776d1bfba95c` | `36d18df5eba0faa86b82749c000343f2ab20d1659d84b4df874c9006e1ee14cf` |
| `Representation.Induction.SplitKernelLocalizationData` | `1239f865167539dde59af69fb6ddf78dfe1de2de3d79b5e42af85e6f5624f4db` | `297331dc35bfc36e8dd7a9a49ea213a49098af78639eb9c1729be2bbc4b38a3d` |
| `Representation.Induction.SplitKernelSectionAction` | `641e8c8436de2e21fbe6268875fb0e09b245574ce3f125cae483f73e66bacfe6` | `351387f15b64867fbd9552e29638ae83873df006c1db6d1d44e54aeb25c24975` |
| `Representation.Induction.SplitQuotientProof` | `88fd875a7768e394179e03bb52d995c666c8872915a0317962dbf547520890b3` | `d032e2ada4b8cc237094c7c8f532a20f9803bfbbe04145a24fa90b1f31a09b2a` |
| `Representation.Induction.SplitQuotientStatement` | `8bb7e8b7edec7c4df971f71118b43ef9ef50efa6c3c21fba001e6caef9855306` | `6095c37c1932fe30de3621cef910ef67962d2f17e5153d3262f42b261c99196a` |
| `Representation.Induction.SplitStagesCharacterComparison` | `5bd82e0ba10c8a51e9565ce5eecdb0a68c40887810aab9ff668a86f2c2658950` | `c7b9b5849b03aef32ba567050ed93f245c502a89597d5e4957a298298329f9f2` |
| `Representation.Induction.SplitStagesCharacterComparisonStatement` | `6b74e219c2387e19ba971d26722bb74f2a3cd839a038a91ee3323d7d146329bf` | `011f54f68a67b62bc5556341f72cedf1d484e7f73d10a9d4b33849bf4c642f97` |
| `Representation.Induction.SplitStagesCharacterIntegrand` | `ba6e65511a46cbf66db088d0317c173269d51e1d3279f9cfddf1b5fba9454fd0` | `819087a1f98f53d7fa105b47ac56383aa22568d5e173a130f652ec0d45806a39` |
| `Representation.Induction.SplitStagesComparison` | `28533fbe9ec55218a30cde943ce8d504b5e9c1e96ee60d9e5bb5ec47e58a6969` | `820904619af53b86161d723b3d2cc394fae4202b7aa58053e0df3879431bb37c` |
| `Representation.Induction.SplitStagesRetraction` | `8d8003cf0ff732fc82a1ed7e967fd49e9a355e7d6a10fb3abf1c8a70c0e97a63` | `94da5b74be696ba20c1addfc677b09be18a972eb1e3e9cb3910c48a89f741a70` |
| `Representation.Induction.StructuralStatement` | `2379edca85c168570183f0ad2673670fbbcb16efbe4bb817ccc60893feb56185` | `eacfe34e82aab124462d814d283f6fab550ba007ec2eb83d1a1e231f5212b9fa` |
| `Representation.Induction.SurjectivityProof` | `270c820487e429cfaad08e8a12afff2a60e08f4db858d2a2eeadc468ea7d65f6` | `b17c3cbdb655954f5ed1933d703e05ea9564656026c4e730d43ef3da40cc7e5d` |
| `Representation.Induction.SurjectivityStatement` | `17a6aaf8c20bc482f4cb6daf2b1814a74b0fcd0d06e35364708e77db3974d05c` | `c20d7705d31e8dac7457d6af49abdad8879882c4cb0773c9dd6d68db20949950` |
| `Representation.Jacquet.BlockCompressionProof` | `9a9600a5ab082515b3714ef581277e279f2a9c2e550fd96ba24fc1d448720f63` | `8e0d6dc5423afbc2c428a6b250861487f742b1df1e6a60a71faa93948b337829` |
| `Representation.Jacquet.BlockCompressionStatement` | `bb8352ead2d715df560862fcd551fdafd5442a5a57256738286fcd56db48f743` | `59d520f9be8569d1645ee19239acbfe3d3a9ae86cebfe38d81fc4558019f49db` |
| `Representation.Jacquet.BlockPowerKernelProof` | `a0e021460f63b190eb987d6710b041e338e13878d1cb1f477fdefe7bd51f7925` | `cfbf3cfe096025494d1bd2847b12b9e4b63960ac7da885b200ac80bcedc3e049` |
| `Representation.Jacquet.CanonicalLiftBijectivityProof` | `3a42ac9168227581d9002f7c6074e8d4c10d226ac1421dfe36b96cfdaaabc875` | `80b3b9a26533ff69eee887d4414459a5af8eb00a448449bb78aa26e29a7bb3ed` |
| `Representation.Jacquet.CanonicalLiftDefinitions` | `17e0facef187fe86529eac390d32e15ba9ab685e04dd42b6a82e0cb42de9044b` | `98ddf1eafa8e1f2c5161ab68ad6f318a1b10db9d84299e69221de6457fccb783` |
| `Representation.Jacquet.CanonicalLiftGroupTransportProof` | `e0ccddf186926ddb05e4d21f34e58ce85aba25f636eb70479501aaf308e7cb2c` | `f9297f114a29cfe34be81e2ad4c0946ea06780a19ffad8037a5cf9d2ac3d7bf5` |
| `Representation.Jacquet.CanonicalLiftGroupTransportStatement` | `f347a30f73d085981e21bfb7699bf1a1320d9476d3916ee73ee4ac9bf9584ebd` | `7e66302401dc740e5f4b241ee069a70397dfbbcd48f343b222896b131231979d` |
| `Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof` | `415afc8f3a40c82e2e5a3ac8e2485741ef6ccc2b3a34b80beb8925ef19743404` | `02ed7f24ae052548b47da67a04e3db64f01151157141b252f88fd00d36a45be3` |
| `Representation.Jacquet.CanonicalLiftIntertwinerNaturalityStatement` | `6bfbab91ba85c83ece7852ade1aadfcce5940b77f9a2b3061dd83fbd14d0c1e1` | `cd81a5b8a29278cd80facdcff4ca5eb60bd6d828b037c115064f10225f557651` |
| `Representation.Jacquet.CanonicalLiftStatement` | `437717a8fe1b896f1f42ae414931ab4d1a961ef68aabe48254929b26e311b05e` | `b6fe3c6e522ca07aea0d920ffc95cc64a3daffcf8e509c82d22c0885dc6dbde9` |
| `Representation.Jacquet.CharacterAveraging` | `3a56eb1cd00d65d0c091f3d436ff88e6d049b0611c0a7ac6eb7c2e43e24e1f1a` | `a907dab19d14a075755dc75231b42aafc2763217fac7cfcf6004c640375b1662` |
| `Representation.Jacquet.CharacterTwistEquiv` | `a0ee45d2a54ec841ba55387ff390528b1d3908bd996a5671507d122a8a05ad7d` | `569e57003979b49ab85b978b06724c6378c8add157f8212e51923ae5f7355834` |
| `Representation.Jacquet.Coinvariants` | `73e5003712204a35595095b0582ad64d931423aeecec2f6165c4c20d945a4566` | `5e040cb16af3b1c72e0c7f1530881639ab055f9528703b9bc20de1931d098a00` |
| `Representation.Jacquet.CompactCompressionStableDualityProof` | `fac2228f79c6c62e7cda199cff8a2d204e912bb3b93e8af75f138c2a9943c102` | `f0245240e3c1904308514c02d3e311af59ab25366c67bf807bf64d495bec6554` |
| `Representation.Jacquet.CompactCompressionStableDualityStatement` | `c365933ace50ff731f2f4ad388aa5e5907c7e808cc826ceefc48aeae74fc6620` | `171eb2076456201eab124aef5921ba941953bda0b7cae6126725d28e6837e3a8` |
| `Representation.Jacquet.CompressionStabilizationProof` | `e3c0dbb92601926e5061681743d8884ecec8c72fb7fdaa4f9cd8fd0b4f4055fd` | `c5c438109ae91808a261c1b293410d3d54a308d16dc062c513cec85d776d68af` |
| `Representation.Jacquet.CompressionStabilizationStatement` | `ff8c8febc8ed825d2ac54c1e095a6e333a40e3b581b4494ce857a4b605824cc3` | `ada20d5266723962dab0d4b41cb25c762841f945bd971feec232c64f93288ab6` |
| `Representation.Jacquet.ExactProof` | `5e813e4fd5da8eac9a4de9de3fa333dc8c024d6509586d71ab12071f4e1252b7` | `28f7303a0037897202e2726ec0accd133e2b294555d94449309cb1c1fad7fa68` |
| `Representation.Jacquet.ExactStatement` | `40b1f46115fb5901f25d178b36a4d3dcc27a2aca9e1bf6be0f6e263238fa229f` | `90a8cfe32f709cd355ae1d6d6d737860d639611450762a72318fc3f6c0b900ed` |
| `Representation.Jacquet.Localization` | `0b50fec4e9e7ad2561f86c6d7e485e2c3a10b1e1c6f750f10c35f5cfc1b3b6ee` | `2a575f90942a22b363b4184941a2470d33e27ad633afe02aa4aa1b818ae62332` |
| `Representation.Jacquet.LocalizationExactnessProof` | `e6589473c2b5275344655346f33cc4f7b6cfcb66c1c60c3427a25e695e7e59df` | `02d434e5101b22d95a86ec5cf9e27d7a0f6897e1c84cca34af4e061f96b95664` |
| `Representation.Jacquet.LocalizationExactnessStatement` | `a9522d236a6d2a3a3bdc53eb844ac00eb1fd885c1afb0f98f61fa4815673e9cc` | `f6613fe26b384516f9d4c3bd0f680af536968d4035067ffd10d664537fca52a3` |
| `Representation.Jacquet.LocalizationTower` | `8d90f6a38e39fb0df3f1d0a9595e428e88e474b5f7e91e8d41d6ec4be8db4a74` | `b78658bf831cdcc2092ae6c420472598d11a4f6c22e01d95eab13a3b4b762c0d` |
| `Representation.Jacquet.LocalizationTransport` | `74aed1b80e686b6b3ddbc3ab87411afaa382706672a9f91268c2a5cf5fe36f8c` | `a25868d84ac803d6be40c52a883fd5573a39351f9a8b9da10d2dca1a4394eafa` |
| `Representation.Jacquet.Normalized` | `e551b389e93bcc14373882dffb4d1c7da02ea388f45e51c0149c04a8b7e93a37` | `f14e1d7f7e803ed7879475c70a2225ba62eaf31b3c6e9d3b834f1a09c5fefb31` |
| `Representation.Jacquet.OppositeCanonicalLiftProof` | `530e2db93879f2a3400ce8496949647f4d59b52f0b001e900842018f7dcdc0bc` | `7d43121322d33541c987b170c9491c4ee7a52eceb6c90ee6370652ad7e238b7b` |
| `Representation.Jacquet.OppositeCanonicalLiftStatement` | `43df581b754165206d8b29b010749395e62da6a72ec8396c56866082981c32ef` | `f743e37facdc9a6b7e0191102d3eb83d67c99e496c2b06e617d5a376fcd99fbc` |
| `Representation.Jacquet.Parabolic` | `5622f725e254efcdfccbf8ea6471ad1835ec2c9842d28b86e30624512abe81ff` | `f29cc93cac2c1dfe4af5164eb4a9e56890f433290bc1e26733eb60545458e6fc` |
| `Representation.Jacquet.PositiveCharacter` | `90891bcc752689f5fc8071e63de8598efecfd17987cd5d804b470ff6ac57df4d` | `0fc44a60a88f7d48415d5e2f804c2837de5fc253eb1520a4ddee2f6ff6414f40` |
| `Representation.Jacquet.ReciprocityProof` | `d2aef6efac12800b55737f95cf795f16a3eee8a2de492da9305378d959841833` | `9d5efc453537681541811010a82e23bcc150823248dc8f80468ae8d540c4b6ff` |
| `Representation.Jacquet.ReciprocityStatement` | `445906e981e46a3b46d2c5beec4bc68a0ef5a70c240a48e3ecea18de65d8dc0e` | `0d358084254d0aed456e9f41aa87d891d4f90789584f33ffa49fc077edc183b5` |
| `Representation.Jacquet.RefinedOppositeCanonicalLiftProof` | `db038f5935cfbc19df792f82894cae9da855ef01dfbf2cd5242b7a5e4512d46a` | `d91711180fa2ec36322c74b7c1c6b956d4caf03fe29427ac70cc3d00ff8c5c20` |
| `Representation.Jacquet.RefinedOppositeCanonicalLiftStatement` | `a51c935ef7e839c45b11b4d313944982eab4f4d2dd2e6a9251a9c8f02a9875d0` | `499e0fc78835e09f80f64de2b432aae7523ee44d908176b5e5b1d2e698ec122c` |
| `Representation.Jacquet.RefinedOppositeCompressionProof` | `7598c30b2cc189c60d5ffd6a2d5601722b01e2fce042e38331aad4f54761810e` | `ef13cebe1c251191426279e930726e785a35bee769567eca312daa3f5d56c36a` |
| `Representation.Jacquet.RefinedOppositeCompressionStatement` | `7e7d8d749f175da14db0bac7e6e728df66500706d7f0459d1caee19b49768c13` | `68f6bce886dee42dfe0575fe25621f280793e9ad322ff4a27b9ef546dc68b729` |
| `Representation.Jacquet.RefinedOppositePowerKernelProof` | `f8d592a6f775fb766923745d4fe806f1eaf1b7dbfd9262214718e6f0c7c7a5bc` | `eebaa5fcbcdfe0a4d87f0da890cf5f04c6b696143a6b1276a29666fe4b9e41c6` |
| `Representation.Jacquet.RefinedOppositeStableImageProof` | `a3059394b94990acb22aae59a2f2f7eb6f24868cb36bd0d1d8f22430378ef42d` | `4c267e64ea72d225c88e19a6e6d12dade86071f9f35241010db1dade3214ac45` |
| `Representation.Jacquet.RefinedUpperCanonicalLiftProof` | `d242f828dc6090df7cd91d3ccf180b4b7e0f83cd658a5451cf3d5e1fbdae70af` | `e563a73111b1592fa6bce11631b246a15492675228ad3622416fdd0342e194fc` |
| `Representation.Jacquet.SmoothTwist` | `61f9309e04c330e87ceaf2f948868645d6d668a0d9dfde75d16435ca355a5daa` | `4c8fa6423740da78ca9a07a79872d36139c9823e5ed0befa880912105823fda8` |
| `Representation.Jacquet.StablePairingProof` | `d1778bd77d9d07686fd407fcb99f651c9bdab36f6513683c929193966dbe2e3c` | `cd708bf1fea28783e9ba12de8c4ee337affa398c758d5df571bcf440a650d36e` |
| `Representation.MatrixCoefficient.Definitions` | `92c0bf57151ef798f1198793a4d685afd175274240c1956b54ce3d10e855b7ae` | `c9fdcc728fe28ed0de403801ed10d861d70dd69994179b4fd14f35662d910955` |
| `Representation.MatrixCoefficient.HermitianProduct` | `2b09a10cff5a80514a5ec9ddaa3724d0543599c29c82bc3593d52f80dc8eff65` | `3f12b2484f21bf5e4d870e312d279ce6c637d2d1d71794fdf79a5b49f41a75c6` |
| `Representation.MatrixCoefficient.LawsProof` | `f73da4941552a524d5e0116675df291d5e99ae1c59b6bc10b21ce2f0ae0fbbae` | `b517f288c98cb53bcb505562f68a20db15025e1c89de85733fec3c8a501b2f6a` |
| `Representation.MatrixCoefficient.LawsStatement` | `bf9b7e4cbef45e07642511fbfb033312f2378714476510549e1c6c9189d570fb` | `c077dcf35c8f1229abc17244c5545fbc17603b1c96ae635ced585c82892d1fdd` |
| `Representation.MatrixCoefficient.ModuloCenter` | `c4ace524d8f5907d58bd12af542354bf9f0438e73dde5e02f93ee4a77614fe56` | `8423b03ac1466c9f87b177f4752a60dd928ca126ef712e2f291dab4b3eae619c` |
| `Representation.MatrixCoefficient.NormRegularityProof` | `7abab3494cb199e4bab82b73671112a32d59c7a626b7cdf111419e7cc5c841b1` | `97bd1a477bdcac30b1f5126d910a3314ccb569c4f52216e56cd69c4f62431bd4` |
| `Representation.MatrixCoefficient.NormRegularityStatement` | `0a369d6c8cdab687dd49ed36350b45b94eba10d87ad8f46c284b08c522aed19f` | `d9353fbec89537409fb6da1e239f458645352e078d8d76e1c2d0d91d582ba5b8` |
| `Representation.Mirabolic.LeftMixedProductSuccessor` | `38068ea224c33865fac13b83429c5ad7036d7aa3b210e3ed3287a7e2db42042b` | `880fb2f156502ec2562ff0e705a0ecb0209a270813196fe7986d8db18ad31751` |
| `Representation.Mirabolic.MixedProducts` | `7a369854d67f65596f0183eba9fa08011ec1a665456f68b8d53e9e3787c5a572` | `d95b20c3198941cdb048a6972a0c7a4c248a223ad9db347e2f92301f61da811e` |
| `Representation.OrbitSpan` | `22fa891bcced0d5a86388bbabcc9fe929f78901b6035e3b95a24eaf46ade4047` | `74bc01ed965646fe444824217f57833631d55f400f68c1e46720016b0765d683` |
| `Representation.Parabolic.AdmissibilityStatement` | `423f1a8a24ea8ec81088c251b7126c5f3a66ff848ddc9d64ddc12906d324c5d0` | `2a055286698a6165bdf902bfb0d502468dd64acd6afcfa6e96191cc4fda16ff2` |
| `Representation.Parabolic.ComposedFlattenedInductionProof` | `3bcb80674e5ebdcf0929b2a9fbe63b3728fa2efe4bd3783e69e8ceed521f6c01` | `d89ba6cc5efe4da412dcdfff57dec3a7e71ec0b4cf8b649981a1f0629f0721e3` |
| `Representation.Parabolic.ComposedFlattenedInductionStatement` | `e7e6ad101becbea3109b05dbe413411b4d7fc64540faba801e2f67039b01ed45` | `f24bf30038f0d29a0592dc9f73ee294813a2814f3a2f11e4fcdf49bc5f2cb3f6` |
| `Representation.Parabolic.ComposedFunctors` | `daa763591d878cf1c668a9a18ca9c29c458cbdc40d3193bd750cbd729cb159ae` | `a093ea026edb420df972e6a348142c78bdf9286f76fda0e08904c21e0f395936` |
| `Representation.Parabolic.FlattenedJacquetQuotientProof` | `3072b0229bf0132b1ee9af80ef835671132dbd0cc23f18698cfbba2e4dfd7a5f` | `2d1863fd318ca66e4ea8e3ba28d9b2fb3a434ced501b98d836d47d353a7ca7f1` |
| `Representation.Parabolic.FlattenedJacquetQuotientStatement` | `64d369f6b38b5bfbdf5f71fc4b1c1f049477d169758b0a0d095d24b012cda2ac` | `24bb1e33a8089964bced23c63662b507ee49dd09aba7441df1006a6b2166657c` |
| `Representation.Parabolic.FlattenedRefinementModulusCalculation` | `48b296b6465c3975d4b95bdc5ec5d8f53148fe727003fb52a804118b8e49f8bd` | `b4dc0864c9eff113510553d14ebea187f1901fb22356b29cb8567c926ba66600` |
| `Representation.Parabolic.GeometricPrerequisitesStatement` | `842bdfec134e48e533c86e8ab58cd0a4630d617bfa1b2453fc2b401d9614bc76` | `4043a06afbbc476c63eea833f08c6cf5cd4325eaada6f362d718e0b2b4499641` |
| `Representation.Parabolic.HeadTailProductInduction` | `225b68c92ffa4b45b9f51b2bf930da380ea7e917ef3d3f757ac6c6736e71b43b` | `a5cb3cebe35cb19c8bc96b6dedf3e24e1d248b909927e4901612e5db85a2e1d9` |
| `Representation.Parabolic.InducedMapSurjectivity` | `4d30adca5351e7c802e6b5e83811d8c0195e4294e6d6bfd0ac0bbd2eeaabf91d` | `e8348beaeee097119664bdbf9223a12e671f4d4b86bf0bccf4667a96301ae407` |
| `Representation.Parabolic.InductionFactorMatchingProof` | `1b6de1ca421a0e37ac95638b6681ac3b802ce077d9f14ca2b9df532d1c99bf1d` | `7a6588d6a422b65603d70725ec3af30cdde26e6dd2bd530ff2f688fe77aeb4b7` |
| `Representation.Parabolic.InductionFactorMatchingStatement` | `66ad43ef90da25cad5437fdbe45edde8a206ca78bb50c98cc4bf10764eb35ccc` | `20725b9e1ed669d4687058828f459c31ab3733217dd34a7a301f077ee3fd0a69` |
| `Representation.Parabolic.InductionSubrepresentation` | `6173ebfdc9b434180fa99f4aab6069807ec9f843a0f0d9ec919d981f1d2aac3c` | `d347805848c860b20addfd8a0f666c456a03372c8b1613304546a73e3064d81a` |
| `Representation.Parabolic.InverseTransposeProductProof` | `8d2f477eb01c0662c0e38d502217f2b0a972d2d9c1f14b41655ad55df790d49f` | `d3777b688439f7c4ee272dbe2766a67a9ae2e3c5f2588293e72de852d86ffc5c` |
| `Representation.Parabolic.InverseTransposeProductStatement` | `03709bc82a01bdb3503c31cbc49a45c2f7b95350da06db820a5b6c585928bf56` | `1595da45cd2469989cdd98d8d903983aeddb8b47f5f04769da48be9f52127b92` |
| `Representation.Parabolic.LeviBridges` | `a284ef13cb6a975d24db64ea673454fa4f1a4cbf651be214c686f0bb88cd3b9f` | `a41c6d9765ecd3c4d207f45a03d19f40d2922d9c8b95f0729278a7ce910d55ca` |
| `Representation.Parabolic.LeviInflationAdmissibilityProof` | `bf7d72238103b15b59127932ef7db03ed4484c371c744552e15ae8899452cc1c` | `adba40c3446c9f6141aceb23176c06d75a87ee555cc6b5d434777cff44ee6832` |
| `Representation.Parabolic.NaturalFirstAdjointness` | `627415c27ae6f6728641c3f09a590255acaa025419c921cb1bfe4387acde60ec` | `592549b38ccb858d59f2677cd55d0b795fb8e2cd58be5ece2d041f04118b6f02` |
| `Representation.Parabolic.NaturalInductionDualityFromScalar` | `17043ddccfd7c71b59f10250720bbd3ab1ab2129f20b248e372d5c4f07040a28` | `b451c0ecf06a0001f039713216d9f7b61e6d861d99e376e72b5b1e2a8bf3ce09` |
| `Representation.Parabolic.NaturalInductionDualityProof` | `18228735df5e207f903da7923e02b45ad31c7ff920e2673a92fd6230a4466f45` | `71776892de7b7b1bccc9bcf6ba74886307034f484b5316b1a74604fa1bb41ff2` |
| `Representation.Parabolic.NaturalInductionDualityStatement` | `e49fbdf7a6181f714b0b9c1b1f32961786a511f065812185982907c1d97c9182` | `1809cdf8b273a3e8dada77de4dd72efdd2271d633b2a8ce3b1d2ceb53628d937` |
| `Representation.Parabolic.NaturalJacquetDualityProof` | `90adb5400326d6b52afc8ec2fbbeeb321c6c073afe4b87b91f70d73a77d8dba2` | `ddf85f7901b4a0d090f01965bdcf0ff91944b04d455da7a770fbaf568e0f3425` |
| `Representation.Parabolic.NaturalJacquetDualityStatement` | `7590db0ed8006906356828b0e79163e5244cf0591d5d7c4aa2e44309cf4c6f1a` | `759a81d02bb708dbd3b2315f19dae800ad10a1b6419c792efbc315c9d8eb705b` |
| `Representation.Parabolic.NormalizedAdmissibilityProof` | `44e2d08a016241d71527e9ac6eeb09a06abe51b290ad4ad5fd70259ec0221c1e` | `7c52be3216dfc3dbd8488cb5e7b9c2fa6aa191f172dae04910c3f9cd482fee91` |
| `Representation.Parabolic.NormalizedCompatibilityStatement` | `31896f590b2f394f7237e2296927410ded686ad3a2cc224d106095d0dc888f88` | `f839c9c1cc2dc5672e3b17e81905daa992313b5b46f4bdb2c8471c2e500265e5` |
| `Representation.Parabolic.NormalizedInductionStatement` | `15c31e074841a316baf63908f17f7c0417f32f1a9918443b09ec5a4db10b78b8` | `e7d5dab09b8550a3e54ceb4852ba287e385db2b6c7d9cbeae4fa8940fa42a2ad` |
| `Representation.Parabolic.NormalizedJacquetAdmissibilityProof` | `b45c2109cd330477c7a0f0bfa565922f12e8868d649323888b75c0a8f0f966f2` | `8293dbcaba6f6d7c2db31b9f8fbdfd269b6f30bc120e666ea5426ee1a4551f4a` |
| `Representation.Parabolic.NormalizedJacquetExactnessProof` | `37afe983ac55ba277fe6fd8652bf0671f32ac009149d0fda5dc2b165c1b98468` | `aebf3aacf9c4c06c1729f569905a37553d40bfb7557f57ba740fd4957bf5c3b7` |
| `Representation.Parabolic.NormalizedJacquetStatement` | `543a1bc79063bc9ef3ad9d03e587d3491240105cec8170ba1596f297c0ff16c6` | `ac1f4c78b6182fc0b2564440c80d8acca373ed1632e748bf3eb460f13421eb41` |
| `Representation.Parabolic.OppositeJacquetAdmissibilityProof` | `928b243bba5437ca7f8dce69d6dfe8e015c9526bc5e3feb27a346b8b249902cd` | `98b8b3dd2c6b408ed8122f1ab06c5129b911e302db4a789d3f95445c7a318d19` |
| `Representation.Parabolic.OppositeJacquetAdmissibilityStatement` | `37f90dfe9ea02c77f1801b1687eea842c8cacccff0715aa523e493f90e7f1fba` | `f6997f3dc7608f463c5825f32e9bc926aa3292d36fbe230cd380713af6025aad` |
| `Representation.Parabolic.OppositeJacquetMap` | `792583aeb45692ed89a535ab92c7b379cda892d2f78f00cdfb836283f6cf91a7` | `5ccb88ac27e3ba1a707be77336e09c50cc76fb0dcffbbcd15fab7b41c3f51478` |
| `Representation.Parabolic.OppositeRefinementDefinitions` | `f56b3ecec27b1c7d06fd5aabd246adb4421076a9d1652bc6839df2a0c56ece2a` | `b9b3cf1ea146812d729425963b31a8b55f3539e477c2c30a15cd469075a88ea6` |
| `Representation.Parabolic.OppositeRefinementFunctors` | `eee6197cc895031cef8b0c14d230b0c580ea9eff1b81b4337be311079e49bce3` | `9940555eb815dbcc9d1b89c9c02788e7936063d5f3d25235315d00529908322e` |
| `Representation.Parabolic.OppositeRefinementTransitivityProof` | `521735f84581753e5c1a0636d7c087f0c2ebd7eddb0b566fac910fa80385b120` | `a2d644e1157da3190cdf62c79085948b601e7718563e1dd31eaea362bbaa0288` |
| `Representation.Parabolic.OppositeRefinementTransitivityStatement` | `9d3c4bb226306b5af6ba620c38c5ec1d7ec2eed2952228b3f9f15584591abfff` | `fb5b30d05743173546e7f1664b6d95da490086092ddfccf977f223ed4f166e9c` |
| `Representation.Parabolic.OrderedProductRegroupingEquivalence` | `b1738cb105dd02beabf3d605f06f12d31f228126457f7197b208d8b20ace381d` | `a8fffc71aeca8c19d90db456212da160ea67a2fb2ee5eb6c64648c77e8e89f72` |
| `Representation.Parabolic.OrderedProductRegroupingProof` | `0cdfba6e59fb73e354253ae0aff8e59fb98d32596dedba9f0effe7b4666c47e2` | `e19d5da5d2509f9e3d0856e0520f79412fa459d4a437feb9a86af99f31b53ba8` |
| `Representation.Parabolic.OrderedProductRegroupingStatement` | `560b539bceb0118ff6bc881f31131b9e401447f3a814b7ba62da222aaa37c325` | `2f20caab78c39b03942e2ca7109028f244b462120c2eba53720aa6400a3c5747` |
| `Representation.Parabolic.ProductInductionSubrepresentation` | `86bafae4da03c2363244f144bad49723be071f9320318c11c5891ea648430aa3` | `448e6c6e60162f586fbd092ce7fa61975875a2292e01271f79760a6162372282` |
| `Representation.Parabolic.QuotientCompactProof` | `6ce7d302d8fbe14375b99e532bfdf9dfbda2e53b21c3b01e4ea6ea0835c22d5a` | `dfe0e388d3e1ea844fd70792bcb1568bb2530c63f5b4b2653f2e4e7597d4e4c9` |
| `Representation.Parabolic.RefinedInductionAdmissibility` | `cb700debf384945084ebf063983776cf7fc166bbe25922a61c494af892c2be97` | `2d8df87c380d8bb5e4fdf47bb14c52e4098b4eebd7f652ccd4ee6268856a5bc8` |
| `Representation.Parabolic.RefinedInductionTensorMap` | `f84cda8c5a38282cdfb31803db8cdcc54fdeb81745b6c74a617e4f70d5589454` | `087775ec1c0506a4cd351cb30ba1296129ea39e232c14e68bdba533bb707a160` |
| `Representation.Parabolic.RefinedInductionTensorNormalization` | `39ba4d9267ccd759939327d3a50f174c69034f490f41c8e96594591dd7eb3ef1` | `020d47733575f02b3d2cfa2315d597a30b75dafd6b4350ae4cfa63f3a13b2e29` |
| `Representation.Parabolic.RefinedInductionTensorProof` | `8392f1d2fb3cc2b25265a83eedf53ec1cbe1a70fc8e5275a4d585eb6eed5f196` | `53d75abbd424b5304a30c8ad3b83499c91a85b3e121397f71e92f8f119fec0b2` |
| `Representation.Parabolic.RefinedInductionTensorStatement` | `53da2142d160bda5acb3154260d1f37d1528f9d9dc2107e3ef2ae3df396fab44` | `3c94c1f292e29c2d3740595dab668271146a561ccea259aa977f9dbabf4f8a82` |
| `Representation.Parabolic.RefinedJacquetTensor` | `af3ef2a5e86d9884f3756f952fcb1039262d3232935b7dc8f916cb2bf299d8d5` | `ec298619d9a5085fe08aca2e92caf7c1a7e33f35d9ef42dfdfc2b0545e7b0f2a` |
| `Representation.Parabolic.RefinedOppositeJacquetTensor` | `4339a7a30a13a0bc4cc3c0c52371badb312bed2158a9d9e15ce098685dd38b2d` | `1f4161c54381e769ab0cc991de89e9f6bb4c89cd778c5458bbaa072fbee32b12` |
| `Representation.Parabolic.RefinementCharacter` | `a9a08b19046a19a72a8d92958276dae15b1395fb47e30c82e985a16979445eb5` | `c2659740483cf1f3dedd85065cf9ef7352e3a166e94a9a63e993fe6694d57ce6` |
| `Representation.Parabolic.RefinementComposition` | `6f227f714838ed282d6fa3de9a049fe5e464a0eaa92f6a7d287352ddd781be40` | `c66a84d2493a528ba5d56b13087f8523d6892d314581889b58b279ee502d8c25` |
| `Representation.Parabolic.RefinementCoordinatesNormalizationProof` | `cb235f1c6cfc0d579171f896f531bbc045d8978634416cf16b5b83f8c3026ba8` | `20b1db8fc343bb810fddefd8818fdd578f1ddb39bd2138b81a934567c6139ecf` |
| `Representation.Parabolic.RefinementCoordinatesNormalizationStatement` | `9d640aa61b7e62bae10cc27e80a1853025ed5e5ab5a3479678e42569151714b5` | `5af76eb69ff7b2616d3b26a9f54781c5a2503d6ba8dc3041f01e369e5779f797` |
| `Representation.Parabolic.RefinementInductionTransitivityProof` | `f3aeab8d6dd81434d8fbdf3a36bcdd201ae34957d466fb8fee249400b230e64b` | `ebef3fd1c97e5dab8fa2228106af2a5c2715724bc5c32e1d1ae97bf57b211275` |
| `Representation.Parabolic.RefinementJacquetTransitivityProof` | `d7a74c23cd4a79d9cc7ca2a072088c2b5a0b6fc33dabeb2c3e8d97c531f155da` | `8334ccceb3f35e72ba3324a5948928027cb3d78ab709defa9582f04ad42e48ab` |
| `Representation.Parabolic.RefinementPreimage` | `bef655c63be1526339d7b46b691c18235d651dadd7616a1c7ebe55236a1e2b81` | `55f7725c49d648d4a1b940d537e36d26fe513fd0b53e1ea800b01e4457918ce9` |
| `Representation.Parabolic.RefinementTransitivityStatement` | `a957a83451ece178d65dfb36aea16cc1a152ec641acecf447fd5eb2d7a0b1c94` | `506b14035be02e030e8637206e8aba3da7affd40b98d905ef0e3e6b1ce31cf95` |
| `Representation.Parabolic.RegroupingFactorEquivalences` | `2fd3f94b10d2c5d606e677ffca0be5910cb8429448b82eaa382e7e5cebd1633f` | `393f6c5f9e28be2aff68f8ddfb8b6deb86c11faa61920d1689ef1ae4ce728237` |
| `Representation.Parabolic.SecondAdjointnessAssembly` | `7854ad789c77a0f460b3c09978ca0acb4dfee066e5cfcff3ea535065f2838b92` | `9ffc8815df9066e25c6b5a6d7a4b694489da9234c05c985794380f36ac86c3d9` |
| `Representation.Parabolic.SecondAdjointnessProof` | `002d4cc869a572f5e76b26dd2f2d0b4a8cfc9d92d96822d95647dbb086af2291` | `117b456db48cd48fbbf31e904fd924279da5f1993a0acf315ebebedce2be986e` |
| `Representation.Parabolic.SecondAdjointnessStatement` | `59208242514b93b66452af980212698ec06d46e293b95159a789baf6260b29d5` | `706f343cdc2b487790cfcd4c81ac3a8670b8ac541cb1bbd43d435739a312bd3a` |
| `Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof` | `f69247552922f39bb5e18bd9f657a6c084a8974d554c5f38463eabc2c7cb7094` | `7d994fc2953f3cab53d39b72f498767e9cea06ecbb0b0b17607c69f8c9d3f387` |
| `Representation.Parabolic.ThreeBlockCarrierComparison` | `939808e20f7aadd14c4aec92fe9a1b6eedcd2e8e57277e8afb43600f4d4d54ab` | `6c9b8d668b6a544223bccede3558b7d068637fc07c057d4c65e371dbe22c1b54` |
| `Representation.Parabolic.ThreeBlockInductionAssociativityStatement` | `efd0220874d72ce5ef2d54ef1850852be6f8899cc0f85b1bb431564eb3a9a60a` | `917d8fa8d18c4a5325c7b1b5448cc8c94f6e09c85d2a911cda652da70f147a3c` |
| `Representation.Parabolic.ThreeBlockRefinementGeometry` | `d372b9943e96c195686cfaec7e2fea1e78f243a476011cdebbfb70b19c5d630a` | `540c036222f1b7ebc5d4ad5263b8195174ff8b31b8a239114925264879a3812f` |
| `Representation.Parabolic.ThreeBlockRegroupingAssembly` | `46552d49d7f8c74ba37cc812b7979d184cee2d2ca54f6e35c2710f399e21c58a` | `35b9d64090766351d64cfc8bdad4584bc45f245efffe6b1670904d5136534194` |
| `Representation.Parabolic.ThreeBlockUniverseReduction` | `b8d095c647559a92691c015694201e3c3e00e7923e92f4feefefbbc585fe6b71` | `7e73fcd8e0a8c3d14d44764453c116d5c5eff199426782d881d9c37d56308d44` |
| `Representation.Parabolic.UnipotentFiniteContainment` | `f79a606e01beca4bc068b6eb36a9ec0b81d2df25a770de1ec18b57a9e177b481` | `23ba8a909a62e7df310cb65f80cd33380bb1014c028a0327ff1b25de56c02e1b` |
| `Representation.RankinSelberg.AnalyticStatement` | `083bd22291a622e1ac8b4f5bbe7c5a13ff5949d0ebfcfc4d180924e2517ec5de` | `74cbeadddca7b4d5ef27d97d98f54913fe78124fe5acc0b20a00686145c5d254` |
| `Representation.RankinSelberg.EqualRankFrobeniusProof` | `92d320fc50696f18219a3dd45543e8850d334a9d93f2f751c8d375aef67c8fbe` | `4cbb5c14ecd0a5c044873e4eb18a28d64e63576f0ea8f4f6c564b5a6f86935b9` |
| `Representation.RankinSelberg.EqualRankFrobeniusStatement` | `67e9b25ee55dfeb0bae9ee5e1b7f14be076b7db1cb25dcb98669c503d70b33ae` | `990f35465df65318e000755c151fb4d261f2650800ca9a47adf92a0853132c0f` |
| `Representation.RankinSelberg.EqualRankTrilinearAssembly` | `fdb3783a5e06ac073d397ff04405e12e574979d2af2d4a6a0709a046f784c87b` | `483f8b662a3dc4c5b0e119ea9d8772d4deb1c917d7521f406319f4bbdc9f9f0b` |
| `Representation.RankinSelberg.EqualRankTrilinearReduction` | `d9cb1e3b6603f78277fe7e78364e9a7094af1eecc57999c9882588b1b75fd51e` | `9b7e3256c077007c029dafdfa06d51bf56d44a76f11b40ba4590f8ded081467e` |
| `Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement` | `bf25a275ae221f34c327b37f510c8c817671f18d02bb5ec0634232a0eb4a3c4a` | `621bd26eb1647faf6475a10aa25accde9c179f7d6f71afe3c7c4f9ba8c024974` |
| `Representation.RankinSelberg.FunctionalEquationStatement` | `d2abd6d09f1cc1155bb8b80e32f5059cc931c1cd8d0d81610c54dedea0b32ce8` | `de240a8838d2919011b77fd1548a5064ac7e35a1980fb99d6edf4b9c7294030a` |
| `Representation.RankinSelberg.GeneralLinearUnimodularity` | `f561b8561777f2e66909364464d102547f0a0449351c933ba1b04012c896eded` | `836cbc09925540740fcac5f6a0b93652aaa6de9c3eb4a09dc0a8132a71e61d45` |
| `Representation.RankinSelberg.HaarSymmetriesProof` | `68606f4a65ffe4e7e75cf3f30d1777f386450062cb3bb17f52724925e8482ea2` | `4fdb5aab2b839e15560a98b43981fdd40348b8e36d59ca0c5726fee6bf54e822` |
| `Representation.RankinSelberg.HaarSymmetriesStatement` | `95af1531c24540e631b8053a8b91af7a5a037c5204690e49af5aa4c8988a89a3` | `91076f2dd053b0f0ba9f60a8415f0f56aa0dde9ddb028a10e5f0e2ccb381b38e` |
| `Representation.RankinSelberg.LastRowCompactOrbitProof` | `f7277986c42ecafc0cc6a6716783c470d60959741a09c9e9054dacad3ebede5b` | `796525a8d8bc340b47ca3768608b74a731ce0d7fbe193b4c0cd82a36c1ee7e08` |
| `Representation.RankinSelberg.LastRowCompactOrbitStatement` | `7df0742492e527dcc84ec45bca21b0e566d9665650ee48d71240f5a22dcfb243` | `f9ad3c415eab0ffc12c2ff58136c2ece6660b9311b1dd0c946d33b329eeb7c3b` |
| `Representation.RankinSelberg.LocalFactor` | `af7cf52dcf557bfffba6dcd468e1f4b2c82dd5632d8c0075b265a5fe2a587083` | `4ee2f81dd1816154d15cd3a345b460f61e29ea984341a4952fe2a3b569d2eeb2` |
| `Representation.RankinSelberg.Measures` | `89c17ab7cfe53fff02eb9e4e35ada34861316e24fe4e30d59dfb911c1f6ab972` | `92af85347233357acc18b92476830b573b22ab85bec8964297201995e28ce911` |
| `Representation.RankinSelberg.QuotientIntegrals` | `54a4db12afe87aaa74c15492767577ae34efceb37d82585e3cb3b8b682425400` | `7df47f60c8acad5982ac6c8bb5c642eba1283cc582034350029961c1332381bd` |
| `Representation.RankinSelberg.RankOneQuotient` | `a13e1dfdb51e9908a37f48ebced825fab380d4e52b90ecb6cf673dad3e3feded` | `1b849405291e0291ddb3a03f5869da566eb36ca4c80b89722ea6b626f2a07a11` |
| `Representation.RankinSelberg.RationalContinuation` | `06cd9b0a4b1fdf7381fb0fb7fc6e8bb2cafb5dbfce643c109b320d0943e49f7d` | `688292f22a7a6cbd3cf3c7bf9ce3e720321ac50de11db4fe557c809fb716eca7` |
| `Representation.RankinSelberg.RationalZeta` | `d7002189349916d9991af7c3ad6e334be1b93fb7b17320e0e943483350f6daa2` | `11086f1c2a1ff39e6b1f7ed0d5942ccd23801dc6c256bfd956e3c94342793f7d` |
| `Representation.RankinSelberg.TwistInvariance` | `3aaff27156e4ff4bea7cf0e702d79afa3a03fc5ba70714cdeee8c727dfb0c397` | `e218df97e8ff7b1d1763275988204d47bf29406fc780331aad86e03809087016` |
| `Representation.RankinSelberg.UnimodularityStatement` | `9bb58fb2a30b86a0dd103569acdace040305196d920941386d7ffb0f3399111b` | `eda1bf92c56147c95d5a5eab81607c2850288e1ab8289a8a3c7ce83ddf7e6cfa` |
| `Representation.RankinSelberg.UnipotentQuotient` | `239aef6b95dabb871b8764da8b821df842461eee5d7998a875105741efb19c2e` | `b78b80f5caa107b33462953d8be304737fca6e000002d368c3471d5ca3ae192e` |
| `Representation.RankinSelberg.UnipotentUnimodularity` | `26ceaee4f6d1731e2fc11a7fefd8d14cdb2ae75820f5fa4a87de6eab3fa93e9e` | `05472ed4788503ec539d606eeb0a513013db4c796e4e71728e842837f04f598c` |
| `Representation.RankinSelberg.ZeroRowLastRowCutoffProof` | `fb2b6edad3a3571b1b83d7b7750ce5f8e2a93ff650fea2f844d109091c95f032` | `ab98129d081292b66f49efa633ad4926030f30a4ab73678c45977040ebf3877c` |
| `Representation.RankinSelberg.ZeroRowLastRowCutoffStatement` | `40ba003edf84fab08c5baa6b71e6b1b7e183d4798342a2c7359083fc800bb924` | `720cb55cc9a99a0c19983e4f2a9dc1f05d0925da91048aeaaf23d5a888710a2d` |
| `Representation.Schur.CountableDimensionProof` | `978778ef06c0733fa6b361fbd3cf4a5c474c1a3cd6ac3e456dc29f9ddc370a65` | `b864801fcedcd600423a6e4c95d944c3040c96f82f6acdd52b831ec625823509` |
| `Representation.Schur.CountableDimensionStatement` | `15d8341f4586685ef5ff8b3a15b666dda44e74c276786fbf072b5dfa5e287d92` | `ce950ef01944267b724886c0655dc8d9b539f7a2f0708077874c018d9182c104` |
| `Representation.Shahidi.Geometry` | `24b8504aab8a49812c128c7782881cbd5fc30ae613ec74a682f19de3fbd5cac2` | `38f784b714a6326afe62e9850b512a3adcf929a62eafc7c1f47b818f25a8accf` |
| `Representation.Shahidi.Induction` | `eed7bfce4a1aa3eeb1ec98354ce2f1fcb25de0d9ccae65108205544e285423a3` | `e71fa54668fe43a47d09c1f7ad317249bd5754e6ab5194560f83c28526ffbac8` |
| `Representation.Shahidi.IntertwiningCovariance` | `cf6137788679530b630342c7fdf8f95f5d721f793a7eee73ac6bec8af3094d08` | `0505f412247bc892060cef36bfb2ee640ff159d467feef3d9d75a034d221c32f` |
| `Representation.Shahidi.IntertwiningInduced` | `69eeccaa31f029c81754a449acaa7b9c1a83ded3b729e10eaa3ff4802306c039` | `1c5c71624e352dcc6907ab6dbcf48216b524b793fb9faa916a3c920f0894e221` |
| `Representation.Shahidi.IntertwiningIntegral` | `b13b18d5deb19bd3e0bb0b35f0821fdea9b1b44484da9859b7bc59f4c0098cb7` | `8a485c0b493ea4677b0db10f2483d934718abc960646c24b109501b5d35c5e71` |
| `Representation.Shahidi.TwoBlocks` | `516b9a555f10e6175431549aae309810afe4f2cffaa0fe16580a7acbc9a8e40a` | `d2f24bdae746307fd1ceb8cfc5b695c5de3f78e76967fccea7f7f27e31ca6ac9` |
| `Representation.Smooth.Admissibility.CofinalProof` | `b01c589f73cb2488a38477ea95bbb6adda0863507efbcb54e561843e467c112a` | `df9117b7ccc80b412fac95816eda27bb0bb18762909c8b0ec39ff35a9a398b59` |
| `Representation.Smooth.Admissibility.CofinalStatement` | `df36b24b8e9972dbaa6d810baa13fcb796fbc81465367c8de92a08ca4449a433` | `7cd745762089838e4cbc5d4e6a96718a7bc7632de6b74c2499e84e59af9911e1` |
| `Representation.Smooth.Admissibility.EmbeddingProof` | `39d5054b926521075ff14f661c16733c8a40e9782b9ba854f66b7d815f8ecccc` | `c43917217a65d2a6b0c1808c5ab739c99d55c5065dca49196ed9e65d131a4808` |
| `Representation.Smooth.Admissibility.EmbeddingStatement` | `8521d3f4c64187dcd24fb55dfd4de9bbe30210eb65df8fd68728bce3ccc7b2d9` | `58845f9496da31d552f760c3ae59db5fc288e143108b9f451e496b8d1ca05e50` |
| `Representation.Smooth.Admissibility.EquivalenceProof` | `304925cb616850278015f3070772e14ba319842c27b75e42b969d73eeeb3f3a3` | `0b0dc7b4c7907ec888d705ad66db522dd365eb6b9db3cd384a73f4f94f52a1af` |
| `Representation.Smooth.Admissibility.EquivalenceStatement` | `e92b32efdaf676556953406f3306fc45d32e685a5f0aa0de1bbe1d9ee0245574` | `a246a8409fb5a769a3324c3b8ba305c1a5c8e2db2797a31176ee311f4b3b57e5` |
| `Representation.Smooth.Admissibility.Extension` | `1c7f1f99500a0f359413d26338aeac172e69490fed126d85f1b3257215fae6f2` | `0bb9c242a8bc69ba4b2707ca74dddd3bbb713708458a9a7d3062e9749bac5469` |
| `Representation.Smooth.Contragredient.AdmissibleDualityProof` | `5635b4f840d709a22782b6db40c49ac3ea8e3ca332f7b0973be862a5fda0b439` | `91d07b8385aee910961e6fb2dd4bd00eb0b134334ba3cbb8b531644b4d94cf58` |
| `Representation.Smooth.Contragredient.AdmissibleDualityStatement` | `a3b9788828170bc1ef481d64332c945c3827876bcf3d12f7c9af7278b1378e09` | `bfb5809f5bfd36bd7b873b7b41932d0777f9f54e70369011b88800d9b15dfc26` |
| `Representation.Smooth.Contragredient.CompactDualityProof` | `5b07a1aaf036dffa1609f488485992513e17ee9aec49c0e002584a7226220594` | `a198bbdda5652427b692f37ddb7326c67e1dd5c95f1b57a8ea531b4dabc334ec` |
| `Representation.Smooth.Contragredient.CompactDualityStatement` | `aecf6195a2703a560242c597cce8c8de908a3be30ef3a12992956cffc7b3550d` | `27b6ba05c0923755f12cb6ed6508cc9fd0f4c1112bf6cdcd1a715a06f70c2abb` |
| `Representation.Smooth.Contragredient.Definitions` | `878b6130d7c563ead853cbdd50a6c70aac01f9104062049e696f9e68cbb30de3` | `531fc58fb846d22f48363964f7fb5af0ab9459747c7ca08a683df6ada7c8aae0` |
| `Representation.Smooth.Contragredient.ExactProof` | `2ef2675f4a84041bb377447eecbf0279bc9ef0336474a6bdb4d6f674f5d7b09d` | `0025ab5e78de3a08d58886b07ce14bcc1344c2cf0f0d6df97b1aec0c1af2c8de` |
| `Representation.Smooth.Contragredient.ExactStatement` | `4608b911207b38b224ec62e444e38a78144a52e923ebb0e63d84051aff559435` | `cda561e6ebc0dae91eafb6f1eaa100e89da8091f9d515eb67227beb662223a58` |
| `Representation.Smooth.Contragredient.FixedVectorsDefinitions` | `3a296f8d4f3235cf43a4114c03ec8debc77d3c8cc23d74b5399e5b756c2ccdca` | `b1e8d0ab28e17dd9affe17f5caf14fb37a6b14e45b4a69d44ac72976d4f52252` |
| `Representation.Smooth.Contragredient.GelfandKazhdanAssembly` | `7f8414c0bc83b9a99cd052171b41ec7bf7b5c9cb60735a924ff1a8bfb1df3726` | `cce2188c32fd3b819d611e7d033983d4b0d3da5f5545aaf2e4520687c73f3ca7` |
| `Representation.Smooth.Contragredient.GelfandKazhdanProof` | `3aa4e3ee79655b8050dc9969c058187cf1a33434cc33f1943c2b71f25ab35d33` | `fbc17917a76d494d4c9034089870823c4bea050f2454c1cfd28eec943aafd891` |
| `Representation.Smooth.Contragredient.GelfandKazhdanStatement` | `1acddaf0533cbf03d7a8cf6dffd5cfe8998424315e36134a7125d89653df7078` | `d95a498616c01041d4f6727ea52c5e1243bcd4045d9fec8b7e610bf7a8b0487d` |
| `Representation.Smooth.Contragredient.HomDualityProof` | `bf74e2e3cc1240d37bd522ba80473a8598bbd2efa2cacbb5e0cae9436cf7ca09` | `bdf43c8899de7443b52c9bd4d651ce1a971fb362e1e10fad19bd4af394877b97` |
| `Representation.Smooth.Contragredient.HomDualityStatement` | `12d47df8361ce30416737f793c462de023e4590117b95013c49d1848ef66c4da` | `507caaf8aa9a4d786864120edaf3bd716b51286c05c2730192103d4736a77c4c` |
| `Representation.Smooth.Contragredient.InvariantPairingProof` | `7a9a70f29b5bdb6e0b251130ce2a429b4f7e5626e9031544717b474d29cb7c10` | `886e609b448d2d69abdd671be5337e092ddeed561d7e083540eefac16827b0af` |
| `Representation.Smooth.Contragredient.InvariantPairingStatement` | `79e580019100d21a88ac3e5b2ce0c170e6139b34195e8072bd7f1d75ec5b524b` | `be187d696a8bb67ca988e720ab72893d86cb17a3b5b83f827de00faadb0f6414` |
| `Representation.Smooth.Contragredient.LawsProof` | `3585eafcf71cca3132c44cbe8da028f346227b8742ea8aa4b86251c343284ae3` | `3e7913a46c581aa48dd58667b01aa41ca79c478140df047375af4faf246a7826` |
| `Representation.Smooth.Contragredient.LawsStatement` | `7de3e69140e0c23094b408621626db56a75e68234d88e1dba74deab77696f24a` | `71ae34dcd1a19591e0b1ddf209b262b6405d9737577dc69065a4c7aaac02e4f7` |
| `Representation.Smooth.Definitions` | `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` | `4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569` |
| `Representation.Smooth.Factorization.MultiplicityDefinitions` | `c8ac6ab5cb7b57650cd68a9386ff62e9c0edbc0668ea77dc9d4c2cd4393f6594` | `7c4a5e4a93ed9bf931fc1a38e4debf8507478d30b2f30e3ebe01149f373d2500` |
| `Representation.Smooth.Factorization.TwoFactorExistenceProof` | `6ecd4d08a8a67c0169941de02f9ebbce2f4ff5d4398f607fc5e59a6e446fb40f` | `feb112128002fced7b893c5e571432aa3de5808312599c86e3e2db76e8acbc9f` |
| `Representation.Smooth.Factorization.TwoFactorStatement` | `0104f1b03db990365889adf5d550956df05cdbe711e01231afa59e72dddd5fbf` | `85b04f03e796a49588c387d26461c1434e78c7960e6d949662b0635f9235161a` |
| `Representation.Smooth.FixedVectors.Definitions` | `4a80076b02e57bd0cc16a38fb21184ea1fd1d7ad723e240831e6a4625a65aee1` | `86568444804fbf3b1afae1edb4cc136756c67422b9523ba8fd0e301599384392` |
| `Representation.Smooth.FixedVectors.Detection` | `fde34e362a28e473cb3ce6bfba709f85414b352a18b11b0781374463569fe43e` | `4977939526a6287bc245f8e232df5cdf55d6b840e95ef78a46f2291f27a3375b` |
| `Representation.Smooth.FixedVectors.FiniteTypes` | `3eada6ba450fb55452a0917998591187c5f0b5ad764d0cc16e178b6c75e70c30` | `e4c94b22e1d150d9c2519c2f9132fe83cb4d1f18e35862c54151e2c8ffdd276d` |
| `Representation.Smooth.FixedVectors.FiniteTypesStatement` | `1511a5ef16092b05c160731c5e21745da761ecc6e454bc56e5a4f4ff80f67326` | `178babbd99cfed8a7d6985e15e843f958944c43fc5e54c3f06b4730424de46d7` |
| `Representation.Smooth.FixedVectors.GenerationInheritance` | `12333e289e0e93d82aec9fa5d9c7148d180d0de64775686b6e9b53f888c560ee` | `fbda9274e7a139cae038c4994d9808fa24c4b09deebdb2a2937ba9b229828f73` |
| `Representation.Smooth.FixedVectors.GenerationInheritanceStatement` | `8f442bb4a9d1c851a2aa87b620b2196ec67c18584893bd80fc2fb5c809bdc11f` | `ed4e25dec2066bc34d6c00540e739bf44b630e821ffba5a532df74de694ddcac` |
| `Representation.Smooth.FixedVectors.LawsProof` | `71c81b26620914f93c7efac3ff1fd918819ffd4d938a53615ffb17849418567c` | `6e75edbe6969dde9aee1bb15c7b3e9b2dafe43534244962925877a371f673382` |
| `Representation.Smooth.FixedVectors.LawsStatement` | `edcd8d356623b3494a1883544f6786d7151683e910b679d4cb694ec2bb743550` | `66ab7ad2d8d00d117c41f08a784266e6d75a34b7d12b3c07f1b1bfbb0133e167` |
| `Representation.Smooth.FixedVectors.OrderProof` | `dbf65e86af4aecd9359ed157ade232cd33ab43c2deef9b6126f9f9bbb1e51ab0` | `8fd46b6860d11058c6a1a076d5387f3ee5cabea1c1ad4e6ccffe1dad7f00453b` |
| `Representation.Smooth.FixedVectors.OrderStatement` | `389c9e2199166192fe43d4be65b8b1bc026fea2378a663c2118301320ab76f07` | `e4615f07daf678bf601a95996369f5d4d602f88f3a768a0c63345b012d58eb63` |
| `Representation.Smooth.Schur.Proof` | `dd696e75f89ad9cf16892022294f516c364aaee914474235b6425299a4d08327` | `ba1bdb5246316e5f6a8f066e8c9bc8d518339d4e31e3590b76141050b9056cbb` |
| `Representation.Smooth.Schur.Statement` | `1eb7a1761466b6eab72cb9b17fbb186562ecd2dc0bbcecbaa012da1094cb3d34` | `082059663ed9d61b60e018ee0475b9836aeef93d171d756cb593eb10e2970b7c` |
| `Representation.Smooth.SmallRealizationProof` | `b3c027565532e7aaa9537e16aebfab4aa34b38b34481383a943abde6ecdd770d` | `dfcdff5bdfc72698c7f11230082f4786ca544819641f9a32e176d588865e06ae` |
| `Representation.Smooth.SmallRealizationStatement` | `f396004c3ab464c9381c85953011be0f7ccb0ab04daa5c538820ef78021e7c5c` | `73cca9a52c32422d2fdf0d3624e498659b9017b0e33f938b4badca82861d2bac` |
| `Representation.Smooth.SmoothPart.BasicProof` | `68683b474202a221a179d5c989b8a5774a40ec80e28093b04821c403a25a28fc` | `aeb2a008caea74aa07c09f1fce5741adf518a63239e239545f2f0c5ba7ad0ed8` |
| `Representation.Smooth.SmoothPart.BasicStatement` | `d98185a4a0c18d4597f28a435391488f294aac6b8ca1280803930cde5b3964b2` | `af69366e079a8fe19ad08051b5185e497acf2a97a85f316ad84a62db01edc470` |
| `Representation.Smooth.SmoothPart.Definitions` | `1362c38a196d6657c4d9dd2388e00c77059fc772bdd7f4369e0cbbee19ca4a47` | `b8775524d5fdc90acf4c52611d96c401e588f6eff68f682843ce999cf414ac60` |
| `Representation.Smooth.SmoothPart.FixedVectorsDefinitions` | `aa6aa3fc09cb94adeb9145f68906b8a9829952ba99bf256659b984a2bf792751` | `5c1be2bfeb8dffa7bd2da042e1511b3d53eee52ef2320b244165dca32e3714a5` |
| `Representation.Smooth.Transfer.GroupEquivalence` | `f1136f8c78bbb6e82bae266b3ad4817cd4e9cbc662cad7f129aae01c8fe10c82` | `da63212ae35532804c6b7bf04df23098331b53f26866983de71555daca8b8f1c` |
| `Representation.Smooth.Transfer.PullbackProof` | `b0502abed8a3551e9a5c542f07605cd66b83649fafbcb38a23b05dddc3e691b6` | `46884ac73c7107c18ce746c2110810d14d19939b7fca6a608670a6c70265ddfb` |
| `Representation.Smooth.Transfer.PullbackStatement` | `a5aaff9766d2e8213ffc82b44625f6fb2ec7f20921b7b03da4ad3250849bcb4d` | `694ccbf90e6fea84743fe380fefdcc25cdaacd1294c53bab78298a465e0df17b` |
| `Representation.Smooth.Transfer.SubquotientProof` | `8e26bf64cb2eff5bfdc6037d5d6c52650bd92944a1c9ef0b57c4f12cc3b0d1cd` | `c1f909953edfa360eacae0f2f266025e1dc1ae7000755873f9ad5d3d2985eb0b` |
| `Representation.Smooth.Transfer.SubquotientStatement` | `d5729f07038515e26eb8d56cc94a982ed8c066a505acea9b1bc2020f4be08c88` | `fea9069973877d67465589b6e5a0d9336d9b1781e7c275c82492a63ce10b3470` |
| `Representation.SubrepresentationLattice` | `1a2d02b46288f8fa370fc2b13b258a408e002120f96c7d5a1294f83fb3a081c9` | `a0c755b61a819917d2ed92ed61aa730d70263e87bbf80a6c7bce35bc7d5ccb8b` |
| `Representation.Tensor.CharacterLocalization` | `e3ae9c4f3aaaffb2c1cdd90593c792c64a72112cf5421bd30a7c01e6b400bd74` | `e36eebe9c642cee619fb3cfcd5130bd31bfa842e4832aa37a5f4bc7539367691` |
| `Representation.Tensor.CoinvariantReflection` | `7513bfd877862c7921a184fe7968dfff6a6f423bd44358056ac30bb62f50e899` | `b4dcd9ed5f344f88a642348fd7c1f9d8107d63661e203b996113960d8477a480` |
| `Representation.Tensor.ExternalFiltration` | `dd54eb315602906b6b6f12bbbcbc8eb2c7e1d4bc28b509f8c9c84391d43d6068` | `4c6b42c71919510b5520cd0b459f54018373bab94e4706746129ec2df25077b9` |
| `Representation.Tensor.ExternalMapSurjectivityProof` | `c3bb1128ddd6ca1d39885a6651711eccd667b64dbd7c6b0a77748f82a1734428` | `3b7aab2d3c4cf53dffe9a784cf2b0267c251d2291ab476b427b1caf16ffe6abb` |
| `Representation.Tensor.ExternalMapSurjectivityStatement` | `4fd6d266973d07481f9a3e640afd51dd71881e66b610fd5e49fb12fe4fcadf45` | `ede3f1c5a63cedcc2794b3f91170b405efba317722363b0a93e45089c0c99c2a` |
| `Representation.Tensor.ExternalSubrepresentation` | `e0a61f7cccbafbca68fb856dae9ce44b9a17105a747c6ba4d909ffdde5e98f63` | `8469ea9b2bf115c55961a5a5a8229705b7a807fa4bb7491826293f7b54958c2d` |
| `Representation.Tensor.Filtration` | `04d0cbe2a8f6766d366a0ffad4c83c50d4a9d6f84034424f3f347a9e097682cf` | `013329c352e5dbcbd60a3990c2f485f88b6f62f754213aacab71a02866acf6e4` |
| `Representation.Tensor.Finite` | `9c5302163726e05fc7c2ee7ba724e14c93edb7ca67c0cc86d003103f0d91d7a6` | `78182d819c69ad5a4840fdf5c453d3dcef0f7b1f620fe680713325113cee530f` |
| `Representation.Tensor.FiniteEquivalences` | `0554cca03ef609b25a05030d827ed82e745d7fe260338567ae0fa6d5ca8f2b44` | `29c420edf5d7618efbdb640920f8bb9c1b5c4662515507691af237404f4c3c44` |
| `Representation.Tensor.FiniteFiltration` | `078110d68ad68be6268938229adc33c7720c50e3a4dab4dd2d340588debdbe66` | `62fc9edc81cc6e3d8117d3c4dee5d4aa9372beb83a7d6b856a066cd33798fc15` |
| `Representation.Tensor.FiniteProperties` | `9b05f123669b22a79afebef2870851b8b62a88719573c9586e0dd0607b8733fb` | `5b529003db64c719e4b25a9a350aeb099c3078a319d4971931b0379e3533e6ed` |
| `Representation.Tensor.FiniteRegrouping` | `b04766b980bed8c37273d45445df8208f8a46eece0379c90f27c10bc933c8a6f` | `e1cd631ad70ff8d7356105508ba2eaccf45b11413203fb5c5b0bf26170b96caf` |
| `Representation.Tensor.FlattenedGLRefinement` | `be96004dda75f152c6e2169e7f188ed656c9ee874d2d6dfe3cfc5f9e22eefde0` | `d6bd2b1a6f97ad513ad2a7e955cfa94f5ffa59eb6f6f5e17419c2d913736e0fa` |
| `Representation.Tensor.GLRefinement` | `e3a4f199a8e8aef358b6510ca79be4dbd69935cd977d0016ab86ddff806f0bd4` | `5a1ada7acac0eeb8be5c4637cb1e485d70ef2389adfd890350fa126748dc38ef` |
| `Representation.Tensor.OneFactor` | `6aa08a047cfc3f7101890ecd51248db8de0aca693d95cb5d1c460590e5c3d504` | `5496c611c4aea14cb8bd9c0c50c03b944d63a9d984a292603a82394de3b8bb4f` |
| `Representation.Tensor.ProductFiltration` | `8464462df6be4fa84ea97d365c5fcd1d28eeb22dedc19f7ae0daff9b2de1be1a` | `81c2c997816198ca03f380adc29dc22e94cf5579e5dd48f5cb2d9d119bf48006` |
| `Representation.Tensor.SmoothDual` | `2f9b933d481739b6c8d2f0347584f16cf70b42336374bd21a586bebe41fdbc43` | `3fbd3821f88c53712c50c05130e2f3ca9064ed0106ae73befbdc3dda2f103217` |
| `Representation.Tensor.SmoothDualInjectivityProof` | `dfdb0f21379af82d5a4292de40bdd6afe84cb815fafc9dead726fd4b8fd37221` | `bc0fd9d65229c65a1ebf9dce2db15ad206acd2980f1b0f9161c6f3c6250a6a6b` |
| `Representation.Tensor.SmoothDualInjectivityStatement` | `2765d4e6f9dbfd0cc2fb22076242774b0d47268737edd5db87b8a8c5ca41f24b` | `1202ff8d550906ad036df57e60b34d376ae424386131cf13007234503d3c98bc` |
| `Representation.Tensor.SmoothDualSurjectivityProof` | `8c8654cbcc56267eab2251fdb6bce3b2db527340b41d1d50981f298ce43575c8` | `9e451da3619acc6fa4f45c5e1682d7bd8978cf70fa34d3cbacdab67806df0da8` |
| `Representation.Tensor.SmoothDualSurjectivityStatement` | `90143a35c08cc841c3825b200e8b0ceda9388d4a37c7b27976aeb3df57c6cf5d` | `9a4a2281e81a7f515f2d6b6a6ed37fd76b31808c4b2975e7d91e27f3f53fb7ae` |
| `Representation.Tensor.UnitaryProof` | `7fe4f7e036a342b1696e5871e9b0356e508f15307d83fbf92ce7a73694d98930` | `5dc08caf26ed44d37dbf64147c0b654d5680bb8e2c2aefe538cc691f6156b7dc` |
| `Representation.Tensor.UnitaryStatement` | `5f4f2b4d5f7d724f5c034846d1efaa7b19f9e9a786aa9e585f2d5750988ddd7c` | `b31149f6c25976d94a9dba5cbe2aa5db768d8dce483686ee7564f1519354043d` |
| `Representation.Twist.AdmissibilityProof` | `706ab8ce915e9902ec30d92c2d471cf7e2e79e2012bf524c9c28868403bf0467` | `25f27ae9ae9c290b60794b1790f6cf0ae47594117c0eee6076dd1cef6b7a0d44` |
| `Representation.Twist.AdmissibilityStatement` | `c875a02d8f49506749bc2265041879888de7ad0c76428211a20ffc755f7e7127` | `04559a67afac5b26f332a6122fd9c43424b35f6d9fa9adf917a186108b7702c2` |
| `Representation.Twist.AlgebraProof` | `15d469011c703f801ddf6810a9104c0588ab917eb2a179ff6360907425c4fad6` | `9d1893be208c8fcbda33b717d999e2767f76eb9068b70f62932fb3de8d0b17b2` |
| `Representation.Twist.AlgebraStatement` | `4c643392e7fc949501dc3e36df71fda5e507598d1a8296be6ea43b3768337895` | `9fd167f7518e27a89b19cfe238a977c8ca2146e0554bb8a92b4dd95171c5b504` |
| `Representation.Twist.ContinuousCharacterProof` | `ff9b38a8e4ded2734ccaed8429df42e2abbf92e580034a2576ad111899820f8e` | `ba9c6c6026b6b6a6b576b0d71dba2f8ce39625451f884fc7fe0a309bd7191dc9` |
| `Representation.Twist.ContinuousCharacterStatement` | `78a1e542d56cbdfe0f0cf448a0010e6ca2f3331fb3af7437e8d03927de7210c0` | `0791b592e84c04c73f41709e1391c23f874061e8991bf57f5bf750dba5367b3a` |
| `Representation.Twist.Definitions` | `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf` | `94e8c64945411e253a2c91a8e1bf52090d6df15a43362b2032717064c6ac49bc` |
| `Representation.Twist.DualProof` | `5a1cbebf252b72d9bc3699d6be57dae2976c4dd47d1efed3ba8b04de07df871d` | `749f18124591244af945b8106de24c7490525579f7c170e1343a323ae02b3e19` |
| `Representation.Twist.DualStatement` | `6186a110b2bcd407bc045388455c87bd7c8d9db8bba41d86749c7fb8e5df1695` | `dd9d380ebac108b80f102a5182f0f15a883f12b4aa2cbe67a76f57a08e55a1e5` |
| `Representation.Twist.LeviRealPower` | `5efb7be5095872533ba970ce5de63ecdab4e794e4d420a45a3979c415d0f0911` | `59cd277b36f1544be0d8d86e5cbcebb8d62dbcd30984a7a281521310c8809f17` |
| `Representation.Twist.PullbackProof` | `8c59ab2c2a3895ef3dc5c9a6ae034d2fbcc22e0074687fa6de6db48b4b7b0f8f` | `bdb6861204f45200c045afbe8d0d3909264daff332aec4ebe2420de9e16d8eb9` |
| `Representation.Twist.PullbackStatement` | `125e3565ca0ade6b060b23f3704135a97b7f24702843b8fcbbd72ac3819439ab` | `9fffc2f10784501ba0cc46842294ef6e366d8209b8f9e4bba16b0dd70a6ae9a3` |
| `Representation.Twist.RealPower` | `83e415568697155665a471b9690d6504e353648839503a9a500ef10601f88896` | `509f3af473e1897d2b340724874834fae55db09fe14bfe5007dcea7eca6e1023` |
| `Representation.Twist.SmoothPartDefinitions` | `80a458acc0486c22aae68602eab0dd30814c31924c82180d151ca217f7029b97` | `b1760e44224b31a1b03e4068aff10563d405feda59c5cbd4e7e4f50b125625b8` |
| `Representation.Twist.SmoothProof` | `704914497f29af5abae486c96edead39aa8fa267efeae2d061016c36634cac90` | `b5423ba5dfe57fe3f53686c01a19fb27df085454007505922a788e5666c8a1e4` |
| `Representation.Twist.SmoothStatement` | `61616bd03710ca5a5c35ba3bb2b4e5793a9f15801ad99a60d7b20bd95ee3de90` | `6e819947725e6a0877bb7d78dba6c2cbe15a6b7f273c4fe531e4ee3fdc31674e` |
| `Representation.Twist.SubquotientDefinitions` | `a9bb92883a9272653ba680cdadc8e025d2f1268bd124ccb7d612f26894227584` | `75aac3b4caadfe14697eeb85f8a4ed729b308d33fd8cac2776c50565de53a7c7` |
| `Representation.Twist.SubquotientProof` | `99a2a6e8fe25e885daffea5e59aa2c77f4304afa100d564adabcd869754365a9` | `cf6dad59297e353be1f3cdeca307c3c507d4fc0a5d29ac1c4806b7edc22c4cd0` |
| `Representation.Twist.SubquotientStatement` | `1c2bae8d080e8c21743d658d1e3a251e4f5c5c997a4ecd2edd77d6d9315d4b7d` | `407963c3e4e87823630f491fca84066dc7d5a0ca1e7c7404d4d1d577905d7732` |
| `Representation.Unitary.Basic` | `dfcb42f377472a4a80c3cdd3ed3fafde80984d3f46a9d189974a24787f5b1da8` | `7cc0d49efa613b15a2fbed1a2884bae0039916d5fda336eeca3b785ee4ea2b74` |
| `Representation.Unitary.CentralCharacterProof` | `10fd1639bab6717064be6974a2704a1093922026c7fb3bd3805985c537af5e9f` | `b4300100dba9d7c51c4d5a0b6ae6e96a208c00cc2bf2052b1558597dd38be953` |
| `Representation.Unitary.CentralCharacterStatement` | `e7911f2b769289a1bc7c5e366a7b296c4aa2b1cd3e048a37df461301ba0c3191` | `180669db16eefca7d887e7215110b4407ace30cbfb45d50283b368ddab3fe968` |
| `Representation.Unitary.HermitianDual` | `fc70ad4e4abeeacdbe9adf71b33050c6903883906d76f8386cb410a5d05259ac` | `f316c1c77ca5043c37989cdcb6d90fa11dd565e52bdfa4fc2542f1e17b15ba30` |
| `Representation.Unitary.LeviCuspidalRealUnitarizationProof` | `6761cbce799cf9facc400577197a93d4ea4fa14214b0a052812dc268b8308112` | `e19096d9c3968b067187017eff4f2642222ebf44cf375de77624e4a72c60033f` |
| `Representation.Unitary.LeviCuspidalRealUnitarizationStatement` | `accf30679bac486d52f4978613efaf5a19fa612bd76f040395721a550cd89124` | `7985710e33e149195773e676ad19071df061874651eea0fd527e05c3311556e2` |
| `Representation.Unitary.SquareIntegrableProof` | `044b3499c873a9a5e1f0aec75e492522176b8fa9174ce59ae53469fab119f81e` | `e0f4b791b0ecc932fc7c6ac4c1d6bdbb7ac48e3488201b5f184141a0dd398716` |
| `Representation.Unitary.SquareIntegrableStatement` | `83b01f64af1dd22cf0475c21f3e2f7c93f64c2bd3ca102ad99d861c5a528e92a` | `c29cfb17b652bdcda071f82aab7179986a73f85f6832aa672589c2ed82c40509` |
| `Representation.Unitary.SupercuspidalRealUnitarizationProof` | `79b766827a897f0e286f29f99bb6ef3c33f3383581a4a1e66881b715bd30620d` | `963bcdcaf1887b84799b8943d995e58589cb0d78eef96117f28da4d1f0f7cb05` |
| `Representation.Unitary.SupercuspidalRealUnitarizationStatement` | `6a81d842d9edf7647a089a9b90d5a167858f4e746becaaa3ede9aa41aae76ab6` | `e93a4f0b0a31345ac82c060f37d1218e0798237f602cfbfa849cf95397462b49` |
| `Representation.Unitary.Twist` | `3ed348a86f5c803820bf27500458d461e75cba8ccafade2653df46374a09a3c6` | `c23cb14ac115cafcf9e328760efa2126f6c075d55b27fbdea23cfcdd271c3a81` |
| `Representation.Unitary.UnitarizabilityContinuationProof` | `754e40020eb2364b2c6852c4fbd824720836ae1460914ff21c396af2f77a65f1` | `aaf404a6ac9baa07be193ed00cd82d759cc130ebe98f44594d96c46701bc224a` |
| `Representation.Unitary.UnitarizabilityContinuationStatement` | `e97207705a6e035c84005a1b95fac1b0c7b074ebab11b383784c5c8020bd96dc` | `a584f9356cabe2f6ce7f6c9c153d98b5adc78bb9b073bbfe2f8f9c8c8ff1e079` |
| `Representation.Unramified.Eigenvalues` | `70545d363717bb6427c09602e6149655b442980989e78e9767215a8b3645e8c4` | `a59b0ac11fe4e022c04af6b7a5949b10c859bc3da2d1ee658a0ab130b8f5a151` |
| `Representation.Unramified.HeckeOperators` | `afac11fae4a02b5f60caabd7ceb3760d6e7618fb7e976be15c258514fb4acff7` | `86e0d538ac90b4aa5b600e7deafd9c0e7d5460f963f3fe6347b8b6faa4ded94b` |
| `Representation.Unramified.PrincipalSeries` | `2709517664211714790ac5a00350ef40afdd8ef30aecab4beed39de2de2b498a` | `5be03bcedd17b31a511d194ac3098c5a647b930cccde1c9d67f7fb3c331f06d4` |
| `Representation.Unramified.SphericalClassificationStatement` | `e7c7c21f68005980398c0a4f25798f68578d836f0eb2a69c5eea7bd80a0515c6` | `9fcf658c2d54270a7a2544c0fa353e2f2274fe84fd2d6a63a4e34a520203ec3f` |
| `Representation.Unramified.SphericalConstituentExistenceProof` | `764cdd80f7ce4385859a5a90554c5529e8193837decd8a2807d85edabfce75a9` | `548ad70fa8f91d07b4ab4c97e707c901901b62695c1be01295b5e9386666abf5` |
| `Representation.Whittaker.Algebraic` | `890e409cf2b4d586912b928755a4a0dc7b72de9d058ede7510482d816dad3906` | `8127b520fe0395c6600d6b72a7340b87edbf38c4ae1ca664546d63452f8e9072` |
| `Representation.Whittaker.AlgebraicTwist` | `37b5426348fa2dffc15702f1ce1a31f8dc483c8354d983ffc059eaae66f4412f` | `a00152f2d8c987a897db2c42e9ad257a4524cbf4b8392c6d641fe458b2abcd71` |
| `Representation.Whittaker.BruhatCellDistribution` | `8b9ce31d93200ddf9eb67dc44f75201da6debcfdc3dcc4de59ff425d2d76872b` | `d1efcfd8e3e2591e2da7ff4275ca0bef18d5e21f882400d97b94d9280f5c7fdb` |
| `Representation.Whittaker.BruhatCellFactorizationProof` | `a28484e18965942bf4a6aa4787de1b1ab43243ad233b4170fe3709a72f41e97f` | `c0428ca8f8a6dfb2d941968c4a9dfb7eaab95e98900d5690cbd9b86c0924d105` |
| `Representation.Whittaker.BruhatCellFactorizationStatement` | `d0937fc620c3e2f1484077d806b468c086502ad2bac8641fcaff9a7788e5b1e4` | `bd774f1f0ecf17a258b5790b5b15e3e330cb79c6d78dc1e0dabe8d5a9c754905` |
| `Representation.Whittaker.BruhatCellInvarianceProof` | `0497857a03a3da72b6d8bc1b329f975eae2334d816641b4ad4f3596099f977fc` | `202f120af3965ee4a83b84acd4cd0252e7be2e4439120ed7e34061eca2d1fe87` |
| `Representation.Whittaker.BruhatCellInvarianceStatement` | `40e62b054155c8965d965ed56313cd7c2fc6cefb8b99310082425acbc99e9a7a` | `cf6361de0ca878e504e92089f7f9d3e5f9c297b9cfa5d13503b9a0bb81ae1afc` |
| `Representation.Whittaker.BruhatCellRestrictionVanishingProof` | `4902a4095f2525245159b1a4442bb9eb4efb471b6a8c1fc6f39bdabde41229f5` | `faf9e00f3c2f398efa2c442fb70b63f7e24cd5d22ac6ff946e2655382b1ccb55` |
| `Representation.Whittaker.BruhatCellRestrictionVanishingStatement` | `2a25e86d2624de3ed7ab0c70c7cc3bf274cbb1c67ac06adcccabb0810ad70ecc` | `e298f18148595942b5560df80e912ea24c64f4e0b02ec9e57f799551c9182de2` |
| `Representation.Whittaker.BruhatCellVanishingProof` | `0450ca2e08621decece86d93c3c21ad6077fdb61a2c3fc3af26323a9b41c6605` | `91ea8e4588ccc60356a9c2b80831d3e8c1007584831a324d00191156c64d8271` |
| `Representation.Whittaker.BruhatCellVanishingStatement` | `a6678c1f7c89d8d7fa7da7c4584de9e397a40ce387fba0466b7be70e75910ae0` | `1bc7d50d275ca9aebf1055fd24de26b87eb4da446a897318555ff530b216578c` |
| `Representation.Whittaker.BruhatCompatibleSupportProof` | `f8276f628c0ac051c8b59b061f605fe3bcb19195ba5d1e2e119ac07cf9d1b187` | `0aaa35cc92e843a6d43484486a666b14ac2cb0a7312c34174baa44c19d7849b0` |
| `Representation.Whittaker.BruhatCompatibleSupportStatement` | `b383eace4776390224d0ed609ab5bcf59d824efadcec0b1b21849bd7f8996200` | `f71a341ba7475dd3c62c5da930fb100ff2f8d6fa5e8f72412125fca850c3de02` |
| `Representation.Whittaker.BruhatFiberAverage` | `631b1ce59410b32345978f66331f9894f7a0e7dc91f4aecd4ff25aa88732c4da` | `bae721ace69ce7741b664749840a73d24b53f8e1940750d8e256d2dcd9bb345f` |
| `Representation.Whittaker.BruhatFiberCharacterCovarianceProof` | `73fa6949c625db98378e63aa8e097a43a38ee02555a87bfccfa86e04325f57ec` | `244435aa6441bf8b2ac3f24f19e7627e2fa549b3132086a5dc78d4cadfb4ea7c` |
| `Representation.Whittaker.BruhatFiberCharacterCovarianceStatement` | `a07533bd75d944b0fd8e617cdcea65052a3e63cc4882843a420780d833203762` | `2569f067e1558faf79382e05f1fee498d9d1b58b79fc4fb32609025bd5ebc73e` |
| `Representation.Whittaker.BruhatHaarMeasureProof` | `9c5670a63adb9866a20a38b7c26bbaa75d57c86e51a0f553b2353d491fe8bc02` | `940ff75b914176a3702d104d8cc94ffbeba00ea37ef5829703bf26efe3aecd5d` |
| `Representation.Whittaker.BruhatHaarMeasureStatement` | `1c7e26c8f534870e76306f9aca25b4dc1337ebd95781e0c95f59a0fc375ef231` | `ba939a8d023e925af34b505b9abcc5ddf6d69f40645d8fea0731780086b717e5` |
| `Representation.Whittaker.BruhatOrbitalIntegrationProof` | `e837243d3f0f05265c94be3b9d498f645a4ab6f20cd1ae2493a3343ed0d7afb6` | `1c5ce3271eddb738ab4a95a36f9b0c21e7fd3358360101b2bd7473733d1bead0` |
| `Representation.Whittaker.BruhatOrbitalIntegrationStatement` | `d40a565d67eba9a1f460ae16e45edac1edc09d272ebe60d35af3988d83fcfd31` | `38fd28fb6adf38d562d77490390745c9fa98f138f7d65de5d58aa4450686c6c5` |
| `Representation.Whittaker.BundledDualTransport` | `d3a2f190fc69ac237c1fd83cd494d2cd2650445a35ac364efb53c76f9359ca35` | `69c23969d574e729be8472e7025f3764f0b156dd012c64f0e2954fd1a44989e6` |
| `Representation.Whittaker.CharacterChange` | `0156e7b1f733656f8c93596ce76c6ff7bcde7f2cd1f18330e41d4a041298abaa` | `cf7605ca7cc468added2f943aabb0565351f3434949491f6320fb3b2cefb2bc1` |
| `Representation.Whittaker.CoefficientDistribution` | `c2ff73106dbac69a53dd65327ae360a86f5870c8363d90fbc8c66818c0f9037f` | `f1774104106bc64e9454573c62fe1cf1a5d4d5b7b799d0d95e21311ccb3ad063` |
| `Representation.Whittaker.CompatibleMonomialFixedProof` | `11d489eb72625ef6993c4a37bc4d25a1977c70b3757ff9e04009aca772b72315` | `72e15332c51e1bcff15b0237996aaa4fd47c063ffdbe614245471ed769a1ec00` |
| `Representation.Whittaker.CompatibleMonomialFixedStatement` | `7c3434178b17b5eacc7811a7efa09652122f84fb837099a119c81e1e59e40f1f` | `9f1af9115219bd98c21dbd13e412c6dd9eee916bf41e11bfb4afadd7eaf04335` |
| `Representation.Whittaker.CompatibleTorus` | `1139128ae883f3a6c3c5274ccf3f8a08b8bd92b2fbb30808779e36ee75a4051c` | `fcab9c107210be8071ad183777b916ef3360f50a1da68c1610f12cfbeef412f7` |
| `Representation.Whittaker.Distribution` | `f87694c65cc6b21c4e1352e54dc4cf5916b89534d5ba7d8bb92d2cc2cbb469d6` | `72b971eed8c58864c0a3360a870d1d272b4ffbb63e6052ebacdcac81b5a46561` |
| `Representation.Whittaker.DistributionInvarianceProof` | `8b2001cef25d74ab9fbfb3d40b06856169bc1ec8eb647d50a7eed72ffab435ff` | `3c3dc2c76ca131aef651c9681f90cacf72a024ff0e629b6ed34a8e69f910c0d7` |
| `Representation.Whittaker.DistributionInvarianceStatement` | `51cc8c86759fa50ad526e646555877c34161f77917333c4d667abc7a256fedb6` | `b5f3335c21681ac3e961128b699114e54d2eb5a57c60d3071e23fec318ee2306` |
| `Representation.Whittaker.DualTransform` | `a82f7ab37f3c534eca18afec42d3692158546b18da8df2f3927cc27721d510b7` | `4e6c51db110a4d4843bf25084975c8c3806896c8a45f4c7a36ef72dc49f38fce` |
| `Representation.Whittaker.EntrywiseCharacter` | `a003fa5cc05ef5abb12a99d0dc2ede09873825fad1e3d169e10327631aa0cfec` | `24a95c28d814d7df3a570ef838688dec21249c5d6ccc9af872b1a4aeaeda1d89` |
| `Representation.Whittaker.GeneralLinear` | `5f5057d690e1bac49a27d650a3c9e678b94660efe8e244ed96e869f33488594c` | `f30d2edde346bc5bbdf3103a54c35f205a6be9643d900be6c4fea23ad38a49cc` |
| `Representation.Whittaker.GeneralizedCoefficient` | `5963796eddeb570358d6015f5bf33c06885bb226ae8594b2354a4655e37b002c` | `faa07305a324aada2351f382229912857306c7596d3b0a5feabcf738e74405a6` |
| `Representation.Whittaker.GeneralizedCoefficientDescent` | `33802bc6bf9bd0941490a848fe7774487ecfa26fdbb094941d3c5ccf7e9570fe` | `d91b8ae914fead9238241bd2f021ba452dfc179c5dd5b8e98dd627cf0e0745d0` |
| `Representation.Whittaker.GeneralizedCoefficientKernelProof` | `6196c1cfde0c5ed75db7dbe7675c206781cc65decd1aae4bb9ecad2b2dc40e35` | `3f64d40cde282e712ce7f15aa4919fb6a54284e201e468fb428dd73bf3322c2d` |
| `Representation.Whittaker.GeneralizedCoefficientKernelStatement` | `ec54d714bf554afc64f4b9361bc199b99c10589fda5cb4e4468d28fa3dc16612` | `56ed8e53a7bab923ae8f54d36e02a31135da067a75af80eecbe7036db03a4fc9` |
| `Representation.Whittaker.GeneralizedCoefficientSeparation` | `36980c0ace3c5f6bacf8e67ae235f4f8ac2299ab94601795f2da97de95e5b2c5` | `d7c134be659ea6934563a5090036fe76b5c7781c934b6cdfb604f567d5a293a8` |
| `Representation.Whittaker.GenericDualTransport` | `0840b53f304005b7521aff871de443cdf8cb79c20f4743545cbc0db971c9ec1b` | `9664f2c08063f88d24a129b7d0b0362d4cf0929f690b022c0e2139bd6bbf1fa2` |
| `Representation.Whittaker.Iwasawa` | `a4a3abc1fcbff7526451cb6e556a9fba0cc1c853b8f7a115e427cd754dfb2306` | `33f35ce22b7688f0f234f7af6141206bf41d39d1658cbc63f6b868b29e7ff3db` |
| `Representation.Whittaker.MirabolicQuotientMeasure` | `35aa2387e99dff16fe655af2b35ef5a7573b73e6409926c2d1bedd0b6a1a0530` | `7201052035dd05c98de11b11f84849af9e0dbb5c8493861341bd244223aacb3a` |
| `Representation.Whittaker.MultiplicityOneProof` | `f454db10b8f7dea1593c4a27064f1bd74bb6b07ae1249ccfd7c088b60177f2fe` | `f3c3db41b19518cb81a77b291c87af8943ea7f99d31e97c9594ba3ff8bb8cfdb` |
| `Representation.Whittaker.MultiplicityOneStatement` | `b3b13bcaa08193dbebf2a3bc4bc3f2e3dd0a71dc04613f026cc050b62bfb507c` | `28fa38646c46020cfc33b9d3840356e9730e639ff8e5ddf8334485f77be4dee7` |
| `Representation.Whittaker.PrerequisiteInterfaces` | `3e3945e0684ac46048b55cb3f27da9982ff7c1d020f6a78ca1cee8c4e5a80820` | `7d30c5ea52a8d0e45626a64117f72a9fb033fd3592f8e328db120abd0c117db0` |
| `Representation.Whittaker.PrerequisitesStatement` | `6db102db4fa4e5cc3bda3cbe773a349fe05060146f90d62972b8e380e9846c6b` | `65d27addd2c39b1c936c15506165fe18cf5099c01ef656e381510cc2fbf719df` |
| `Representation.Whittaker.Twist` | `f0c5f986650dc04bbcfc13e144104e72c92a8e61a44246f33ad1e02b4e8b814b` | `f51654a146f72bd402f86926b608efd23e4154a210dece95b2915ca3f8cafb35` |
| `Topology.CompactNormCharacter` | `6f70b9473d6386cd111d890c4df0bf411842d28dfdc377e38c2c4fe55e8b0fb7` | `3e50c9561e3e7a068e729aec594ce107f572b2858cd859e6c000fcb8c0aef482` |
| `Topology.CompactOpen.ConjugationStabilizer` | `937bc745da117c665bcfd701dbef5758e9ad26f1f4268450c895affa53e91507` | `3dc3ce8f96da8e0525890cadbcbc1d85708c5ff797977e09f7d3af0d613a5c83` |
| `Topology.CompactOpen.NeighborhoodBasis` | `5b5322b631663241c1295826da02d7a43cc585566124c5a426020c19c642a6b9` | `0b258f936bb5e0d99be3608077bcdc7da3a2b885aaed75b2c273a633fe2cea7e` |
| `Topology.CompactOpen.NeighborhoodBasisStatement` | `80d23d1a0faa606af6610f3a306b130c28739e12d51f533c52862fd45a220131` | `f5a2a0045ab6a79fc96e5681a78be891c9f16fcd9514126b87f4625aeb761532` |
| `Topology.GroupAction.FiniteOrbitProof` | `ee3641cc58add211c0f83c216daf767dd2ed6489d61517d07463cfe5f774b8d2` | `fbd5daebc055c402906a7f8646a0fc0e5f1f670baf5841f118e3abecc4d1040a` |
| `Topology.GroupAction.FiniteOrbitStatement` | `7cb833bc7c61b2e9ad177423947dc0be7b901d64717ebbfd3c90b4dc5155b434` | `48d33280c821ba7e6bfbec1da9882fb90c0c7c2ed7f26d841e1c4f688c78cc4c` |
| `Topology.Nonarchimedean.Subgroup` | `a45ededd3f67a6645df268d1bf9da0cbcac964137c448ef89966630cd4b4c026` | `01724029b2c592535f55fea2ec4a857a7d15d15156063567d1216e1e4b265675` |
| `VirtualRepresentation.Exact` | `fe31746d4f005a09538224671bf9fbcda4327e0240640b2678ec392b891ad086` | `b1c7c9dcb29d718fd827e4a92ea146bb6e91bf89a16c43433fdedc143f96e199` |
| `VirtualRepresentation.ExactTwist` | `e874aac5d03ac5725639a770638ed3c1753f1d051b1ce4c5cd9fecbc77b616ef` | `06f9bce02b3de83995ac3675db84153cae3f34032e147e8f6353de118668cea8` |
| `VirtualRepresentation.Integral` | `785418baa91b4ed140707b9a2a4acdd05b0f6ef9dab0efe3f271e2fef76a652d` | `676c34871f15c312e0fed03e9c2231c5109cc98986251ee075afa4c472f0790c` |
| `Weil.Algebraic` | `a7c4651e692c5368802732fc344a99bdca22140ba35238684ad46fe2cb9a5da7` | `0a93572cc4956df7085c6024121f40f5446178acf07cab6b653207c00b511154` |
| `Weil.AlgebraicProof` | `c9619175e9b1ec1b3e22ab4f42a132c3a7b92fb9770766e51da3b5d388d2389c` | `6e55facba45a7e38be7b9564c8682f6b7e21ee0c2fbbf426d150261bad2e20c3` |
| `Weil.Local.Assembly` | `576d8ad3c15763bdf047c2289beea60530c5d95a70963395444fd1efbd49cad8` | `6fb1c6a6e8e5a6ba9748ed021c5050bbca06589072e1ef3d26af0d850beb8b83` |
| `Weil.Local.DegreeCharacters` | `f93ff5bdd74ce036c69453f9d00c879f611ae40608e0c06cbd6b25e5441ebac0` | `e36c1be82694626685fe60a916656d6c988f25410a9eef0297d27cef53b26556` |
| `Weil.Local.Parameters` | `411478f2fd50ec77e62978dbc2352f5d3511bdb4d9d8cfc99e040c73fca8b551` | `d50514551ca4f1b87e21fbf5e24aac8b4b49b10074fc8e21701a4e23e4ef9897` |
| `Weil.Local.ResidueCharacters` | `8f47ed222e4b3b933bbce66918b67f14803267a2c211a1756f25d3fe4aac3833` | `bc28623e170fe498ca85ea98365be018188010cc9d78818fcebbce129bdd6776` |
| `Weil.Pullback` | `1dd3491a90d6849c98bd49a0abd9fa684313ef2b040c9ab11bc49d3967cd6380` | `c0e3920055cbff41b823da174209cb8531e528672b3ed271a90270209b9f101c` |
| `Weil.Representation.Basic` | `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b` | `054c95aeedaac6c9a64148af625f83b3ff67cdea4571f8bb8db62b07b5f18897` |
| `Weil.Representation.CharacterLine` | `36cfc58ac71540b41cb22c6bcada722eba2745ec1647468dab661bac104dd409` | `eb984632d0e1a1180051ee46d3550394badac36632b879efbe68ccda1fbf4f86` |
| `Weil.Representation.Continuity` | `eee2597523d9d1d9a295004aa895361618ece11bf8b6547b9ee5cefa48fd62ab` | `14b3d17fed09138b9f5ef6f11d5e354297933a0a06eb8c0b4260c69e76d339fa` |
| `Weil.Representation.ContinuityProof` | `4ce22049c58e40ae458a0590d7d57d8dbcdf50b33c921a7e4a15ff3ae3216987` | `79b6e04ad4d4a373244b672b2df7c0543eb135506995f99d99ce9d912eea1377` |
| `Weil.Representation.Determinant` | `9a327d3755e33b6b585efc2f2545583a64239044cb0e9cb99a913fb7116ebac3` | `3cc27aeaa01475a34ab8761552cd4c83a2c26dfd722038900dac118f02ae2741` |
| `Weil.Representation.DirectSum` | `b0d730015d7456225937210ba69093a92e268cdde0454d4ed035742ed27e91e1` | `8d5bbb91ce30dca0d1c324ad1601d24f5d3f25fbd400b7e0e091bf11f9c73b25` |
| `Weil.Representation.Dual` | `38cafaca417661df1fd2462cb71fcb880341c4fc561de35797c8b713229a8f74` | `c1157a048325e178598142f3802f888ae0204046f5b4f9792acd59ee4bb80efe` |
| `Weil.Representation.DualClasses` | `126e2e2b73cfe0df928a452c87814c63678b60656158c57e8a1a0b277bac1d7e` | `a96c15617998e39175581a10503031912b87fbf4b7421b0e0cf1d76e62461996` |
| `Weil.Representation.IsomorphismInvarianceProof` | `70dedd491878b8c35701fb089a1da6fd5bb29debeffdbc3d7c84ab55e30f1df8` | `d3cf35211d60684f8bc5c70ac83a415ab2e7bfd5315fbd31f1600fd985630ad7` |
| `Weil.Representation.OperationClosureProof` | `542d89c859c7e2b2c012117c7f2430abe7d1efc585ce1112c492ca9a4bcf7eb7` | `919299539829d1232e7ec8ba6c83f5e4e1db6aafff5ed960ee8899417fe0235c` |
| `Weil.Representation.Operations` | `283dddd18a7022d99ba6e7ab4a2b497053f48582996fe4c9502826f994836dd9` | `ce8d2f16e48caa747cebb7ff4cda07b7abcb2541432c890b465e7969ca505761` |
| `Weil.Representation.Predicates` | `c2bb56c14f6bb674ac9ee78b458392bf59973f53d7e72fd159b7e7a83030a148` | `53e1dcd5efc3ce9b3eac0cae00f0b08569d9f1f8798aa21aa8d1ec1550b9785d` |
| `Weil.Representation.Twist` | `cbeda9cff731f24d07c356c7e24e5e9a20a6e248fc9439bc0888cc909ab862c8` | `e40746180302829880c6c62e027e6550a8f0d1bc17f678b8013af28dcae34c41` |
| `Weil.Representation.TwistClasses` | `210fff747f1e61d891964ce70aab930b7203083797d717ada60eadc68e0448a8` | `6e5cc554e67e7e7b5d374986eeb055aeebf63831b027b1c203f0c03ac10e762a` |
| `Weil.Representation.TwistProperties` | `8d7eb2432681176885dd220819826e4dc8f10a6e564964d19b084b0a9f51a87d` | `d014f1a08dd61177c2ef326429203f26240874a1ea7658617ececdf2875391ea` |
| `Weil.Topology` | `a4ea4bce2df51fc95b343b0c6c779c785dd635ae6fb95ce01496346b4b05c836` | `43b927f69cc74936639be50fe0f003250de93b6e43970ffeed1583ec31484224` |
| `Weil.TopologyProof` | `b6a91adefbd38a70d1102ae25b59000b2dd0d3e8290f9b27be891289d9e33f97` | `192cc9bf157782df7218e7ecfd18adfb7bdb36057ba43f5e03b63634e5f1307a` |
| `WeilDeligne.Basic` | `2359916cf05537665a83a6f5e75c55f2698577b47d9777f6431262fd1b595fbf` | `2c3631c1825b6c950a73e0d9451cfc3f9e191f06a0b0f8d51a08951ad4bd6dfe` |
| `WeilDeligne.DirectSum` | `a8ec6276d9edcf0f8e811559c982e9ba03deaa2803c7ccaa22c77d26669e6907` | `709e157026bd37f2027d050610c16664c7252102a14b8d568a280f826d831bb5` |
| `WeilDeligne.Dual` | `f93dac4cc8e4a22401bff9a548fca0d3103439ae2c859bcd08d833c9d74f12e9` | `555669ebd774b367224089ec100e1480201d1c67fda9bf5f664d9dbcac3b7e43` |
| `WeilDeligne.ParameterRelations` | `29d82698b08437c8230780ae06d36818cc62708cf164be30aa9ea6bb77a00c66` | `3012083002f45d4dfee70f6909fbf2a19f19703229d923b557c27af57e17a773` |
| `WeilDeligne.Parameters` | `73663a8250d1bdc055a419d6574169de0278ee17e26cc457841be3ff6b38898c` | `372bc4b5bdcc3581e8d1c77291f200a453ca65a8d46f7d9c8d1e793e9a90d196` |
| `WeilDeligne.Twist` | `772f17a7cd090d61a70b7a410aff4b7a0ba14609b5687d378497f696f345faa0` | `0f40c11ead0b066811db46182a12ca507cbf4efd9ef8e1795d05db0cdde297a7` |
