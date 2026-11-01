# Top derivatives of supplied increasing adjacent-product quotients

This internal prerequisite defines
`TwoSupercuspidalIncreasingProductQuotientTopDerivative` and proves it in
`twoSupercuspidalIncreasingProductQuotientTopDerivative`. It derives the result
from actual published Jacquet, derivative, support-shift and multiplicity-one
constructions. It introduces no new translation of an external assertion.

## Exact scope

Fix arbitrary prime `p`, `F : PadicField p`, supplied topological data `T`,
and a continuous nontrivial unitary additive character `ψ` for `T.topology`.
The universes `uF,uV` are independent. Let `d > 0`, and let `B,A` be actual
bundled supercuspidal representations of `GL_d(F)` whose carriers belong to
`Type (max uF uV)`. Suppose
`A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass`.
Thus `A = νB` at the existing isomorphism-class level, with the published
residue-normalized determinant twist.

Let `P` be the actual normalized induction of the ordered family `(B,A)` for
the positive block shape `(d,d)`. For every supplied invariant subspace `S`
with `S ≠ ⊥` and `S ≠ ⊤`, put `Q = SmoothRep.quotient P S`. The conclusion is
that the actual derivative of `Q` of order `d+d` is nontrivial and has complex
finrank one. This uses the published `generalLinearDerivative` at its
explicit bound `le_rfl`. Neither the existence of `S` nor adjacent
reducibility is asserted.

## Implemented proof

The helpers in `TwoSupercuspidalTopDerivatives` establish the following facts.

- `isAdmissible_rankCast` removes rank transport by equality elimination.
- `finrank_generalLinearDerivative_top_of_nontrivial` proves that any
  irreducible admissible positive-rank source with nonzero top derivative has
  top finrank one. It writes the rank as a successor, transports admissibility
  and irreducibility through the rank cast, and applies the published
  Whittaker multiplicity-one argument
  `SupercuspidalDerivativesProof.finrank_top_of_multiplicityOne`.
  Supercuspidality is not a premise of this helper.
- `support_of_product_subquotient` constructs the displayed inducing
  multiset as an actual supercuspidal support of an actual irreducible
  subquotient. The witness is the supplied block family and its actual
  subquotient presentation.
- `supercuspidal_singleton_support` constructs singleton support of a
  supercuspidal object. The actual one-block induction equivalence
  `singleBlockNormalizedProductEquiv`, followed by the identity reindexing
  equivalence, gives a surjective intertwiner onto that object.
- `irreducible_support_of_rankCast_equiv` removes rank transport and then
  transports irreducibility and the singleton support along the supplied
  actual representation equivalence.

`increasing_quotient_top` proves the concrete result. The supplied proper
subspace shows that `P` is reducible. The first projection of
`TwoSupercuspidalAdjacent.adjacentStructure`, with its associated-filtration
and nonassociated-subquotient premises supplied by their proved closing
theorems, makes `Q` irreducible. The actual quotient map makes `Q` a
subquotient of `P`, giving support `{B,A}` and vanishing of every proper
positive derivative whose order is not divisible by `d`.

The published middle-derivative theorem identifies the rank-cast derivative
`X = Q^(d)` with `A`. Consequently `X` is irreducible, nontrivial and has
singleton support `{A}`. Suppose the top derivative of `Q` vanished. Every
order `j` with `d < j < d+d` is not divisible by `d`, so it also vanishes.
Thus `d` is the highest nonzero derivative order.

Apply `highestDerivativeSupportShift` with `ω = Q` and with the identity
embedding of the irreducible `X` into itself. It gives
`{A}.map (twist 1) ≤ {B,A}`. Rewriting the class equality as equality of
cuspidal data, `RepeatedCuspidalSupport.upper_not_mem_of_shift_le` contradicts
`A = νB` belonging to `{A}`. This obstruction uses freeness of the first and
second integral cuspidal twists. The top derivative is therefore nonzero.

The first conclusion of `CuspidalSupport.cuspidalEmbedding` gives
admissibility of the irreducible `Q`. The general multiplicity-one helper
then gives finrank one. The public closing theorem supplies this proof for
all the parameters of the proposition definition.

## Dependency audit

Recursive inspection of the five direct imports gives 795 project modules,
including this entry. External imports belong to Mathlib and Lean. This
count includes modules reached through proposition definitions that are
not used as proved hypotheses. The following proof routes, rather than
the location of a source file, establish the relevant independence.

The adjacent-product input uses the two-factor geometric filtration,
minimal nonzero Jacquet descent, nonassociated vanishing, actual first
adjointness, Jacquet exactness and two-step Jordan–Hölder matching.
Its associated and nonassociated premises are supplied by the geometric
lemma and the proper-refinement vanishing proofs. The argument starts with
the supplied subspace; the conditional adjacent-reducibility and
nonadjacent-irreducibility propositions are not instantiated.

The middle-derivative input composes actual Jacquet equivalences with the
partial-derivative/Jacquet and partial-derivative/tensor natural
isomorphisms. The supercuspidal top factor has dimension one by the proved
mirabolic nonvanishing and Whittaker multiplicity-one route. Nondivisible
derivative vanishing uses the actual two-block comparison, the surjective
partial-localization quotient, and geometric-lemma Jacquet vanishing for
actual subquotients. None of these steps uses a derivative Leibniz formula.

The highest-derivative support-shift input uses a supercuspidal embedding of
an individual irreducible representation, uniqueness of its cuspidal
support, smooth contragredient exactness, the ordinary dual and character
twist of normalized induction, and the proved highest mirabolic derivative
pairing. Its derivative quotient-support helper uses the geometric
filtration and the positive two-block comparison: a nonzero map descends
to a full-source piece, factors through its first tensor block, and gives a
support submultiset by Levi tensor factorization and cuspidal association.
The embedding is obtained from minimal quasicuspidal Jacquet descent and
first adjointness. Support uniqueness uses reverse association of two
actual cuspidal inductions with a common irreducible subquotient, proved by
minimal Jacquet descent and the associated filtrations. These are
individual embedding and support results, not global decomposition by
support or ordered quotient coverage.

`SegmentSocleDerivativesStatement` enters through the published
support-shift theorem. Its imports include multisegment, ordered-head,
trivial-group-quotient, segment-product and tempered proposition or datum
definitions. No conclusion about ordered heads, quotient coverage,
multisegment classification or tempered classification is used here or in
the support-shift proof. The used support-shift proof is the pairing and
geometric argument described above. Other segment-edge proposition
imports enter through nondivisible vanishing; their only used helper is
the elementary identification of a flattened Levi.

The new singleton-support and rank-transport arguments are elementary
actual equivalence and quotient constructions. The generic dimension-one
argument uses admissibility and irreducibility explicitly. The
multiplicity-one proof uses coefficient kernels, distribution invariance,
contragredience and Haar symmetries. Integral twist freeness follows the
proved central-character argument.

No used proof depends on the host's excluded analytic segment
classification, ordered special-head existence, special-head multisegment
exhaustion, general ordered quotient coverage, tempered uniqueness,
regular or square-integrable exhaustion, or
`SquareIntegrableLanglandsClassification`, including renamed versions or
proof successors. No global support decomposition or full multisegment
classification is substituted for a local argument.

## Remaining host obligations

This theorem does not construct a proper subspace, prove existence of a
segment head, compute derivatives of a product involving that head, or
prove rank-three irreducibility or composition structure. Both actual
repeated-cuspidal triple transfers and their ambient extraction/refinement
remain obligations of the host task.
