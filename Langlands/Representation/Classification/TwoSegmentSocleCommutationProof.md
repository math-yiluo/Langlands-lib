# Commutation of two unlinked segment socles

Author: Worker 491.

`Langlands.Classification.twoSegmentSocleCommutation` proves exactly
`Langlands.Classification.TwoSegmentSocleCommutation.{uF,uV} F T` from
[TwoSegmentSocleCommutationStatement](TwoSegmentSocleCommutationStatement.md).
Its outer telescope is `{p : ℕ} [Fact p.Prime]
(F : PadicField.{uF} p) (T : F.TopologicalData)`. There are no additional
theorem-valued inputs. The field universe and carrier parameter are independent.

The conclusion is an actual categorical isomorphism between the two normalized
induced representations of the supplied blocks. The datum and its permutation
keep the given blocks, segment labels and multiplicities. The proof preserves
the supplied topology, standard upper parabolic, positive half-modulus
covariance and right translation of the published definitions.

## Implemented proof

Write `v = max uF uV`. After installing `T.topology`, let
`d : T.SegmentProductDatum.{v,uF} n` have length two, supplied segment socles
`hs`, and unlinked segments in positions zero and one. Let `σ` be the
published adjacent swap at zero.

First, two elementary lemmas establish the hypotheses needed by the lower
irreducibility theorem.

- `SegmentProductDatum.isUnlinked_of_length_two` extracts an index from each
  occurrence in `d.multisegment`. Each index is zero or one. Equal-index
  pairs use `Segment.not_isLinked_self`; the distinct-index pairs use the
  given hypothesis or `Segment.IsLinked.symm`. This includes equal segments
  occurring at distinct positions.
- `SegmentProductDatum.rank_pos_of_length_pos` uses `d.degree_sum` and the
  positive degree of each segment. Thus `n > 0`, and the proof writes
  `n = m + 1`. The quantified rank-zero case is impossible from the existing
  datum hypotheses.

Permutation leaves the multisegment equal to the original one:
`Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm d.segments)`. Consequently both
orders are unlinked. The socle witnesses for the permuted datum are
`fun i => hs (σ i)`, which definitionally refer to its supplied blocks.

The published theorem
`unlinkedSegmentSocleProductIrreducible.{uF, max uF uV} F T` now makes both
`d.induced` and `(d.permute σ).induced` irreducible. This is the sufficient
direction of the segment-socle product criterion, used twice.

Each individual block is irreducible because its socle witness includes
irreducibility. Therefore the published theorem
`twoFactorProductConstituentCommutativity.{uF, max uF uV} F T`, applied to
`d.shape` and `d.blocks`, supplies
`HaveSameJordanHolderFactors` for the actual two products. Its swapped
representation agrees definitionally with the representation of
`(d.permute σ).induced`. No finite-length hypothesis is added to the final
theorem.

The generic lemma
`Langlands.nonempty_equiv_of_isIrreducible_of_sameFactors` then turns these
facts into a `Representation.Equiv`. It works over any field and acting
monoid, with independent carrier universes for the two representations.
For each irreducible representation,
`IrreducibleMultiplicityProof.compositionSeries` supplies an actual
length-one composition series and an equivalence from its graded piece to
the original representation. `HaveSameJordanHolderFactors` supplies two
actual series and their factor matching. Two uses of
`jordanHolderSeriesComparison` compare those series with the length-one
series. Composing the five equivalences gives an equivalence between the
original representations; the final length-one index is zero by
`Fin.fin_one_eq_zero`.

Finally, `SmoothRep.mkIso` turns this equivalence into the required
categorical isomorphism. Composition-factor commutativity supplies only
factor matching; the independently proved irreducibility of both products
is used by the generic bridge.

## Original source and derived provenance

The registered source is A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)*,
Ann. Sci. ENS (4) 13 (1980), pp.165–210, literature ID
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The statement's source correspondence is unchanged: §3.1, pp.180–181,
describes the increasing-product segment socle; Theorem 4.2, p.184,
provides unlinked-product irreducibility; Theorem 1.9, p.174, provides
composition-factor commutativity. Their combination gives the two-factor
case of Proposition 6.4(1), p.189. The implemented proof uses the
independently published proofs of those two inputs and proves the generic
Jordan–Hölder bridge here. The elementary datum lemmas are internal
consequences of the published definitions, rather than additional analytic
assertions from the source.

## Dependency audit

The four direct imports are:

- `Classification.TwoSegmentSocleCommutationStatement`, the unchanged target;
- `Classification.UnlinkedSegmentSocleProductIrreducibleProof`, supplying
  `unlinkedSegmentSocleProductIrreducible`;
- `Classification.TwoFactorProductConstituentCommutativityProof`, supplying
  `twoFactorProductConstituentCommutativity`;
- `Filtration.IrreducibleMultiplicityProof`, supplying actual length-one
  series and importing the generic Jordan–Hölder comparison.

Both representation-theoretic inputs were independently accepted and
published before use. Their final theorems have independent field and
carrier universes and require no external criterion, commutation or
classification premise. The application at carrier parameter `max uF uV`
matches the target's actual datum.

At Library commit `e9121d2f8e2a84b24a5c3d710d82082ab261845c`, a recursive
inventory of these four imports contains 1,314 distinct `Langlands` modules,
with no missing project import. Including their roots, their respective
closures have 80, 1,311, 558 and 12 modules. The inventory follows project
imports recursively and scans code outside comments for the excluded
proposition names and corresponding lowercase theorem names. These counts
describe imported source, rather than the smaller set of constants used by
the final proof.

The irreducibility implementation proceeds by degree induction through the
highest derivative. Its substantive inputs are additive-character
existence, `SegmentSocleProductHighestDerivativeProof`,
`NonjuxtaposedSegmentSocleDerivativeStrictMonoProof`, segment endpoint
combinatorics and integral-twist freeness. Its nonzero-product helper
`RegularHeadExistence.nontrivial_normalizedProductInduction`, in
`RegularLanglandsHeadReduction`, constructs a compact local section of the
actual induction. The generic two-quotient lemma in `HeadQuotientCriterionProof`
does not assert a segment-head classification. The finite-length helpers
used by the derivative proof are generic subrepresentation arguments.

The constituent-commutativity implementation uses inverse-transpose
reversal of induction, smooth contragredients, Gelfand–Kazhdan and finite
length of products of irreducible blocks. It does not use the finite-length
generalization of two-factor constituent commutativity. Its generic
filtration pullback and cancellation helpers do not introduce a
representation-theoretic assumption.

The audit distinguishes available proposition definitions and conditional
assemblies from proved inputs. Imported statement modules define
`OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
`OrderedMultisegmentHeadExistence`, `MultisegmentHeadExhaustion`,
`SquareIntegrableLanglandsExhaustion`,
`SquareIntegrableLanglandsClassification`, `TemperedBlockUniqueness` and
`GLRegularLanglandsExhaustionStatement`. These definitions do not supply
their conclusions. `OrderedMultisegmentHeadReduction` contains the unused
conditional assemblies `orderedMultisegmentHeadExistence_of_conversion`
and `orderedMultisegmentHeadExistence_of_prerequisites`; their internal
references remain within that unused assembly. The imported
`multisegmentSocleExhaustion_rankZero` is an unused rank-zero boundary lemma
in `SegmentSocleProductData`. None of these declarations is used to obtain
the two-factor result or either substantive input.

In particular, the proof does not use the conclusions of
`AdjacentUnlinkedSegmentSocleSwap`, `AdjacentUnlinkedSegmentSwap`,
`TwoSegmentHeadCommutation`, `OrderedMultisegmentSocleExistence`,
`MultisegmentSocleExhaustion`,
`SegmentEssentialSquareIntegrableClassification`,
`LinkedSegmentSocleGluing`, `MultisegmentHeadExhaustion`,
`OrderedMultisegmentHeadExistence`, `OrderedMultisegmentQuotientExhaustion`,
`TemperedBlockUniqueness`, `SquareIntegrableLanglandsClassification`,
`SquareIntegrableLanglandsExhaustion` or
`GLRegularLanglandsExhaustionStatement`, nor their excluded proof
successors or transitive proof dependencies. Shared lower definitions and
generic infrastructure were checked separately. The present proof is an
upstream two-factor input to full-product lifting and linked gluing.
