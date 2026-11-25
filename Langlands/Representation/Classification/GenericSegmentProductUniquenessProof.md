# Unordered uniqueness for unlinked special-head products

`Langlands.Classification.genericSegmentProductUniqueness` proves exactly
`Langlands.Classification.GenericSegmentProductUniqueness.{uF,uV} F T`
from the unchanged `SegmentGenericStatement`. For two products of supplied
special segment heads with unlinked segment multisets, an actual categorical
isomorphism exists if and only if those multisets agree.

## Scope and conventions

The outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
There is no additional theorem-valued hypothesis. Every positive ambient
rank `n + 1` is covered, including rank one. The field universe `uF` and
carrier universe `uV` remain independent. Segment bases, supplied heads,
induced products and derivatives use the target's saturated carrier
universe `max uF uV`; no resizing is assumed.

The actual smooth complex representations use `T.topology`, normalized
induction from the upper block parabolic, positive half-modulus covariance
and right translation. `HasSegmentHeads` refers to the supplied strong
irreducible quotient of increasing segment induction. It is distinct from
the segment socle. The proof assumes this relation for each supplied block
and does not assume an unconditional choice of individual heads.

The multisegment is the multiset of the finite segment family. Nonlinkage
permits repetitions, and all equalities of cuspidal contents and segment
families are multiset equalities. The theorem allows independent
enumerations and independent supplied block representatives.

## Implemented proof

The proof chooses an actual allowed additive character using
`HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T`. The choice is
internal; the target has no character parameter.

Apply the published `segmentHeadProductIrreducibility` to each supplied
datum. Their nonlinkage hypotheses give irreducibility of the actual
products. The published `segmentHeadProductCuspidalSupport` then gives
genuine supercuspidal-support witnesses for their complete cuspidal
contents. Its witnesses exhibit actual constituents of normalized
cuspidal inductions.

For the forward implication, unpack the given categorical isomorphism
`i : d.induced ≅ e.induced`. Transport the second support witness to
`d.induced` with `heS.of_iso i.symm`. Apply
`Langlands.glSupercuspidalSupportUniqueness` at the positive total rank
`n + 1` to equate the two full cuspidal multisets. Finally,
`unlinkedCuspidalContentInjectivity` reconstructs the segment multiset
from that content under the two given nonlinkage hypotheses.

For the reverse implication, equality of segment multisets identifies
their cuspidal contents. Rewrite the second genuine support witness to
give the same support multiset for both products. The published
`segmentHeadProductTopDerivativeNontrivial` supplies nonzero full top
derivatives of both products, for the same chosen character. Apply
`CuspidalSupport.fixedSupportDetectedEquiv` to these two irreducible
objects, their common support and their two nonzero top images. It returns
an actual equivariant complex linear equivalence between the supplied
products. `SmoothRep.mkIso` converts that equivalence into the categorical
isomorphism required by the target.

The latter constructor implements representative and enumeration
independence. It unpacks the two genuine support presentations, matches
the fibers of each cuspidal datum by equal occurrence counts, and uses the
actual isomorphism between inductions from representatives of the same
data. General associated-cuspidal induction factor matching transfers
the second irreducible constituent to one fixed ordered cuspidal product.
The published exact-functor detector for that product gives actual
equivalences to both constituents with nonzero top image. Composing
these equivalences supplies the result. Repeated occurrences remain
separate finite indices throughout that construction. Factor matching is
an intermediate step; the returned map has an actual inverse.

This reverse argument uses only the two globally unlinked products of
the target. It introduces no adjacent-swap hypothesis. It makes no
assertion about swaps inside an otherwise linked larger product.

## Published inputs and independence

Every input is imported by its Library Lean name. The closing
proof is internal assembly of published results; it introduces no new
definition, statement interface or external mathematical assumption.

The product-support proof uses the primitive head quotient maps,
external tensor and normalized-induction surjectivity, actual ordered
regrouping, determinant twists of supercuspidal representatives and
occurrence-preserving finite sums. Support uniqueness uses genuine
constituent presentations, tensor cuspidality, reverse cuspidal-induction
association and tensor-factor association. Reconstruction uses integral
twist freeness, interval linkage and induction cancelling one segment
occurrence at a time. These routes have no dependence on the excluded
classification conclusions.

The reused irreducibility proof composes the independently proved
unlinked sufficient direction with a linked-pair obstruction. Its
sufficient direction detects every irreducible subquotient by the top
derivative, using highest-derivative pairing, terminal/initial support
and finite length. Its converse compares the original binary product
with a union/intersection replacement, then contradicts replacement
nonoccurrence using an actual constituent at the very same terminal
witness. Arbitrary-family reduction preserves the selected occurrence
indices and supplied blocks.

The common-support equivalence constructor is already in that proof's
published dependency closure. Its actual body uses general cuspidal
factor association and exact scalar-top detection, with no segment
classification theorem. The top-derivative constructor is likewise
already in that closure and uses the proved individual-head top line
and the finite-product top-line equivalence.

Before reuse, the irreducibility proof's publication in the Library, its
Lake build, its exact target and its unchanged inputs were checked. A
native recursive audit reproduced its 1344 project
modules, 2688 nonempty paired files and 324 external frontier imports.
Every pair agrees with Library commit
`f931c96e65d20b436d2363a83d6971f9406ec738`. All direct-import closure counts match the published proof's
inventory. The direct comparison, pair reduction, unlinked detector,
terminal-support adapter and fixed-support equivalence bodies were
inspected in addition to their documented inherited audits. Previously
completed product-support, support-uniqueness and reconstruction
audits remain applicable to their unchanged sources.

The restricted support-proof branch occurs only through the final
`segmentHeadDerivativeSupportTruncation` theorem, called by
`SegmentHeadProductTerminalSupport`. Removing that final proof from
traversal removes `SegmentHeadSupportStep`,
`SegmentHeadDerivativeSupportLengthTwo` and the two restricted
supercuspidal proof modules. The stronger `core_mid` intermediate is
used only within the length-two base case. The final theorem invokes
none of these intermediate results separately.
`SegmentHeadJacquetReduction` and `TwoSupercuspidalProductStructureProof`
are absent.

The eligible foundations are the independently proved general derivative
route, eligible general infrastructure, the independently proved final
support-only bound, the stronger intermediate restricted to its length-two
base case, and the reducibility import solely within that restricted
branch. These restrictions determine eligible foundations and supply no
mathematical premise.

Neither this theorem nor its inherited proofs use multisegment
exhaustion, ordered strong-head existence, quotient coverage, ordered
conversion, tempered uniqueness, square-integrable Langlands
classification, square-integrable exhaustion or regular exhaustion as
proof inputs. They use no proof of this uniqueness result.
The occurrence of its Prop-valued definition and conjunction entry in
the unchanged `SegmentGenericStatement` does not assume it.
The additional broad name-scan hits concern precedence predicates,
ordinary shape head/tail refinement and the general
`OrderedCuspidalProductHeadShift` argument, whose body uses BZ77
Lemma 4.7(b); none is ordered strong-head existence.

## Original sources

The target is Zelevinsky 1980, Theorem 9.7(b) and §9.10, with the
irreducibility clause of 9.7(a). Printed pp.198–201, including the full
§§9.7–9.10, and Kudla 1994, printed pp.369–371, were read.
Section 9.1 fixes the special-head convention. The registered retained
sources are:

- `zelevinsky-1980-induced-ii`, A. V. Zelevinsky, *Induced
  representations of reductive p-adic groups II*, Ann. Sci. ENS (4)
  13 (1980), 165–210, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  The direct uniqueness passages are Theorem 9.7(b), printed p.199,
  and §9.10, printed p.201.
- `kudla-1994-local-langlands-nonarchimedean`, S. Kudla, *The local
  Langlands correspondence: the non-Archimedean case*, 1994, SHA256
  `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
  Theorem 1.2.5(b),(d), printed pp.370–371, gives parallel context.

The implemented route is the support reconstruction and actual
detected-constituent argument described above. It does not assume the
printed classification comparisons used by Zelevinsky's original proof.
The imported proofs document their original general
Bernstein–Zelevinsky derivative, cuspidal association and support
foundations. No separate applicable errata note was found in the
supplied literature and project source notes.
