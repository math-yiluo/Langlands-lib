# Graded refinement of actual Jordan–Hölder factor matching

Author: Worker 122. Provenance: internal derived module theory.

`Langlands.gradedJordanHolderRefinement` proves exactly
`Langlands.GradedJordanHolderRefinementStatement.{uK, uG, uA, uB}`.
The coefficient field, monoid, and two representation carriers retain four
independent universes. The theorem has no additional premises. It imports the
published statement unchanged and uses the published
`Langlands.actualQuotientSeriesLift` from
`Langlands.Representation.Filtration.IntervalLiftProof` at each carrier universe.

For supplied filtrations `f` of `A` and `g` of `B`, and a permutation `perm`
of their graded indices, the hypothesis supplies a pair of composition series
and an actual factor matching at every pair of graded pieces. The proof lifts
these supplied series to intervals of the original filtrations, concatenates
the interval chains, and composes their factor equivalences. All factor maps
are `Representation.Equiv`, so they preserve the linear structure and monoid
action. Every factor occurrence is retained.

## Lifting the supplied series

The private helper `refinement_of_lifting` chooses from the hypothesis, for
each index `i`, a common length `m i`, simple-factor filtrations `s i` and
`t i` of the two graded representations, a permutation `e i` of their factor
indices, and an equivalence at every matched factor. The choices use classical
choice; no composition series is assumed beyond these existential witnesses.

The published lifting theorem applies to the consecutive invariant subspaces
of `f` at `i`, and of `g` at `perm i`. Filtration monotonicity supplies the
required inclusions. The published `LengthCriterionProof.quotientRep` of
these consecutive subspaces is definitionally their actual graded
representation. Thus the lifting theorem yields covering relation series
`cA i` and `cB i` in the original invariant-subspace lattices, with precisely
the required interval endpoints.

The actual equivalences supplied by that imported theorem come from quotient
projection on representatives: for `S ≤ T` and adjacent subspaces `U ≤ U'`
of `T/S`, the successive quotient of their preimages is equivalent to `U'/U`.
The projection restricts to a surjective equivariant linear map onto `U'`,
and its inverse image of `U` is exactly the lower preimage. Descending to the
quotients therefore gives a bijective intertwining map and hence a
`Representation.Equiv`. The imported proof also transports irreducibility
through this equivalence to obtain each covering relation.

Write the lift-index equivalences as
`a i : Fin (cA i).length ≃ Fin (m i)` and
`b i : Fin (cB i).length ≃ Fin (m i)`. The local matching is
`(a i).trans ((e i).trans (b i).symm)`. At a source chain step, compose the
first lift equivalence, the supplied graded-factor equivalence at `a i j`,
and the inverse second lift equivalence. The identity
`b i (eqv i j) = e i (a i j)` aligns their intermediate representations.

## Finite concatenation and actual composition series

`sigmaFinSucc` splits a dependent family over `Fin (n + 1)` into its first
fiber and the family of remaining fibers. It is the index bookkeeping for
`concatenate`, which works for an arbitrary relation `r` and relation series
whose endpoints agree with a supplied sequence of vertices.

`concatenate` proceeds by induction on the number of intervals. For no
intervals it uses `RelSeries.singleton`, a length-zero chain, with the unique
equivalence between its empty factor-index type and the empty dependent sum.
For a successor it concatenates the first interval with the recursively
constructed tail using `RelSeries.smash`. `finSumFinEquiv` and `sigmaFinSucc`
combine the factor-index equivalences. The theorem proves not only the
bijection between all steps and the dependent sum of interval steps, but also
equality of both endpoints of each corresponding step. The local elaborator
options follow Mathlib's analogous `CompositionSeries.Equivalent.smash`
proof and leave kernel checking intact.

`assemble` applies this lemma to chains of covering relations between actual
invariant subspaces. Its permutation labels the interval refined by each
chain; it reorders chains by the inverse permutation before concatenation.
The resulting chain begins at bottom and ends at top. Covering relations give
monotonicity, so `ObjectRepFiltration.ofSubrepresentations` turns it into an
actual filtration. The published `hasSimpleFactors_iff_covBy` proves that all
its factors are simple. Equality of the corresponding endpoints identifies
each new graded quotient with the original interval-chain quotient, yielding
an actual representation equivalence by reflexivity after rewriting.

## Matching every global factor occurrence

`matching_of_chains` assembles the first family with the identity permutation
and the second with `perm`. Let `eA` and `eB` be the resulting bijections from
global factor indices to the dependent sums of interval factor indices.
The global equivalence of finite index types is

```
E = eA.trans ((Equiv.sigmaCongrRight eqv).trans eB.symm).
```

The shared label is the original index `i`; the second assembly already
accounts for its position `perm i` in `g`. Thus this bijection includes both
the permutation of graded pieces and every within-piece factor permutation.
It proves that the two assembled lengths are equal. Substituting that equality
supplies the common length and index permutation required by
`HaveSameJordanHolderFactors`.

For each global factor, compose its first assembly equivalence, its interval
factor equivalence, and the inverse second assembly equivalence. The identity
`eB (E j) = ⟨(eA j).1, eqv (eA j).1 (eA j).2⟩` aligns these maps. This
constructs the required actual matching with multiplicity, rather than only
an equality of lengths or sets of constituents.

Finally `gradedJordanHolderRefinement` discharges both lifting premises of
the private assembly helper using `actualQuotientSeriesLift`, once at `uA`
and once at `uB`.

## Scope and provenance

The construction covers length-zero outer filtrations and length-zero
interval chains. A repeated filtration step or zero graded piece needs no
extra hypothesis; the supplied simple series is lifted by the same theorem,
and an empty chain contributes no factor indices. No positivity case or
nonzero graded-piece assumption is introduced. There is no finite-dimensionality,
blanket composition-series existence, global finite-length, group, smoothness,
or admissibility premise. The final proof uses only `propext`,
`Classical.choice`, and `Quot.sound`.

This is an internal algebraic derivation from the published filtration and
quotient definitions, the interval-lifting theorem, and Mathlib's finite
relation-series operations. The companion statement's account of BZ77
§§2.16–2.17 explains the representation-theoretic motivation: exact induction
can produce filtrations with nonsimple graded pieces whose factors must be
refined. The present field-and-monoid theorem is derived module theory, not a
verbatim BZ77 claim. The proof does not establish induction exactness,
supplied-series uniqueness, or the block-association theorem.
