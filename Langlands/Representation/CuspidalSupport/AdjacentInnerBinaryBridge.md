# Actual adjacent inner inductions from the supplied binary product

Author: Worker 289.

This internal adapter constructs
`Langlands.CuspidalSupport.adjacentInnerInductionIso` and proves
`Langlands.CuspidalSupport.adjacentInnerInductions_irreducible_iso`. They compare
actual normalized inductions inside each block of the common adjacent merged
shape. Their hypotheses are precisely irreducibility of the chosen ordered
binary product and an actual categorical isomorphism from that product to the
reversed product transported by
`Derivative.generalLinearRankCast T (Nat.add_comm b a)`. It introduces no
additional classification or commutation premise. It does not itself assert
an occurrence in a Jacquet module or the host Jacquet interchange theorem.

The field universe `uF` and original factor-carrier universe `uV` are independent.
For `A : ∀ i, SupercuspidalRep.{uF,uV}` on a block shape `B`, inner induction has
carrier universe `max uF uV`. The host can instantiate `uV` with `max uF uV`.
The supplied prime, field `F`, topological data `T`, normalized upper induction,
positive half-modulus covariance and right translation are retained.

## Two-block comparison and the literal cast

`twoBlockRank C hC` proves that the first and second block sizes of an arbitrary
two-block shape `C` sum to its total rank. It eliminates the length equality and
uses `Fin.sum_univ_two` and the shape's sum law.

`twoBlockProduct_eq F T C hC A` identifies the binary normalized product of the
two factors, after rank transport along `twoBlockRank C hC`, with
`(T.normalizedProductInductionFunctor C).obj A`. This is equality of actual
bundled smooth objects, including their carriers and actions. The proof
reconstructs `C` as the positive binary shape cast along its total-rank equality,
using `BlockShape.ext_of_size`. The positive-rank branch of
`binaryNormalizedProductFunctor` is the published product induction on that
binary shape. The dependent factor families are heterogeneously equal by
function extensionality and the two possible indices. The private
`rankCast_productObj` and `productObj_congr` justify the object transports by
equality elimination.

`twoBlockProduct_reverse` deduces irreducibility of the product induction on
`C` and an actual isomorphism to product induction on `C.permute Fin.revPerm`
with factors `fun k => A (Fin.rev k)`. Irreducibility is transported along the
rank equality by equality elimination. For the isomorphism, the supplied
binary isomorphism is mapped through the original total-rank cast. Its target
then has two consecutive casts: first the literal `Nat.add_comm` cast from the
reversed total rank, then the cast to the merged total rank. The published
`Derivative.generalLinearRankCast_trans` identifies their composition with the
reversed shape's total-rank cast. Proof irrelevance identifies the equality
proofs. The two instances of `twoBlockProduct_eq` complete the actual categorical
isomorphism. The block permutation is not substituted for the literal rank cast.

## Singleton slots and the adjacent specialization

`oneBlockProduct_reverse_eq` proves equality of product induction before and
after reversal of a one-block shape. Every `Fin C.length` label is fixed by
`Fin.rev`; shape extensionality and heterogeneous extensionality of the factor
family give the equality of actual induced objects.

The theorem uses the published original and reversed tensors from
`AdjacentMergedTensor`. Their parabolic inductions are definitionally the
product inductions of their displayed factors. It splits on whether the outer
label `m` equals the merged position `j`.

At the merged position the inner shape has exactly two blocks. The explicit
`adjacentBlockEquiv_val` formula identifies inner labels zero and one with the
original global labels `j` and `j+1`. Rewriting those dependent labels allows
the exact supplied binary hypotheses to feed `twoBlockProduct_reverse`.
Away from the merged position the inner shape has one block.
`isIrreducible_normalizedParabolicInduced_singleBlock` applies to the actual
irreducible smooth inner tensor; its irreducibility is the first component of
`adjacentInnerTensors_cuspidal`. The one-block reversal equality provides its
isomorphism. All outside factors, including repetitions, are retained without
any condition on their labels or isomorphism classes.

The result is, for every merged slot `m`, irreducibility of
`(T.normalizedParabolicInductionFunctor (B.adjacentRefinement j hj m)).obj
(adjacentInnerTensor F T B j hj A m)` and a `Nonempty` actual isomorphism from it
to the analogous object for `B.adjacentReverseRefinement j hj m` and
`adjacentReverseTensor`. This is the local induction comparison used by the
separate occurrence-transfer proof.

The definition `adjacentInnerInductionIso F T B j hj A hpair hiso m` uses
classical choice on the theorem's `Nonempty` isomorphism at slot `m`. Its result
is the actual categorical isomorphism between the displayed original and
reversed inner inductions. The definition retains exactly the theorem's binary
hypotheses, and the theorem separately retains the irreducibility conclusion.

## Provenance and independence

This is a derived internal coordinate adapter, not a new transcription from
external literature. Its mathematical inputs are the published adjacent-merge
length and label laws, the actual adjacent inner tensors, the positive-rank
binary-product definition, rank-cast composition, and the full-group induction
argument for a one-block shape. The last argument preserves irreducibility
through surjective group maps, a character twist and the actual full-induction
equivalence. No associated-induction matching theorem is applied.

The four direct imports are `CuspidalSupport.AdjacentMergedTensor`,
`CuspidalSupport.AssociationReduction`, `Induction.BinaryProduct` and
`Derivative.Iteration`. A recursive import audit at Library base
`8d926c3850083c700afa54adc0d07240e27fe799` found 178 project modules including this
entry, with 98 distinct direct imports from Mathlib or Lean across that closure.
None of the project modules contains the excluded classification targets or
their named proof successors: `SegmentEssentialSquareIntegrableClassification`,
`MultisegmentHeadExhaustion`, `OrderedMultisegmentHeadExistence`,
`OrderedMultisegmentQuotientExhaustion`, `TemperedBlockUniqueness`,
`SquareIntegrableLanglandsClassification`, `SquareIntegrableLanglandsExhaustion`
or `GLRegularLanglandsExhaustionStatement`. Their lower-case closing theorem
names are absent as well. The corresponding excluded tasks are
`aca8805b-054f-4d56-8045-12db7f623404`,
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`,
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`,
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`,
`52e97845-36bb-457d-b76f-70753334b88c`,
`1cb45da2-7007-4351-a694-594fb148b8d1`,
`cd8ab97c-0b78-4bce-97c4-d307a28159a4` and
`bf433f0a-921a-428c-b0c0-6475438125ac`.
The implemented dependency route above also uses none of their conclusions or
any disjoint-support decomposition. The imported association reduction is used
only for its proved single-block induction lemma. This audit concerns this
adapter's closure; the host must also audit its other inputs and establish the
actual subquotient transfer.
